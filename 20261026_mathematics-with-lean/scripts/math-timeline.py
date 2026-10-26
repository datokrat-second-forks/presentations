#!/usr/bin/env python3
"""Generate static/images/math-timeline.svg.

The style, the milestones up to 2023 and the Mathlib curves up to July 2023 follow the timeline in
Leo de Moura's Marktoberdorf 2026 lectures (leodemoura/Marktoberdorf2026,
static/images/timeline.svg). The 2026 Mathlib size (2.2M+ lines) is from the Eindhoven talk
(20260604_DFMD); the curve between July 2023 and June 2026 is a straight-line interpolation.

Edit EVENTS and run `python3 scripts/math-timeline.py` from the project root. Lanes are assigned
automatically so that boxes and connector lines do not overlap.
"""

from pathlib import Path

FIRST_YEAR, LAST_YEAR = 2013, 2026
WIDTH, HEIGHT = 1280, 760
X0, YEAR_W = 60, 82     # x of the start of FIRST_YEAR, width of one year
AXIS_Y = 440
BOX_W, BOX_H = 164, 50
GAP = 6                 # minimum horizontal gap between boxes in one lane
MAX_SHIFT = BOX_W // 2 - 14  # maximum sideways shift of a box from its marker
# Lanes in order of preference: (distance from the axis to the near edge of the box, above?)
LANES = [(60, True), (50, False), (128, True), (118, False), (196, True), (186, False),
         (264, True), (254, False)]
CURVE_H = 220           # height of the Mathlib curve at MATHLIB_MAX
MATHLIB_MAX = 2.2       # million lines

# (title, date label, year, month or None, highlighted)
EVENTS = [
    ("First commit", "July 2013", 2013, 7, False),
    ("Lean 0.1", "June 2014", 2014, 6, False),
    ("First course @ CMU", "January 2015", 2015, 1, False),
    ("Lean 3", "January 2017", 2017, 1, False),
    ("Mathlib", "July 2017", 2017, 7, True),
    ("Zulip community", "February 2018", 2018, 2, False),
    ("Lean 4 begins", "April 2018", 2018, 4, False),
    ("Perfectoid spaces", "2019", 2019, None, False),
    ("Natural Number Game", "October 2019", 2019, 10, False),
    ("Quanta article", "October 2020", 2020, 10, False),
    ("LTE challenge", "December 2020", 2020, 12, True),
    ("LTE main result", "June 2021", 2021, 6, False),
    ("LTE completed", "July 2022", 2022, 7, True),
    ("Lean FRO, Mathlib 4", "July 2023", 2023, 7, True),
    ("PFR conjecture", "December 2023", 2023, 12, True),
    ("Equational Theories", "September 2024", 2024, 9, False),
    ("FLT project starts", "October 2024", 2024, 10, True),
    ("AI: IMO gold in Lean", "July 2025", 2025, 7, False),
    ("Carleson's theorem", "July 2025", 2025, 7, False),
    ("Navier–Stokes", "September 2026", 2026, 9, False),
    ("Quasi-Riemann hyp.", "October 2026", 2026, 10, False),
]

# Mathlib size in million lines, as (fractional year, value). Converted from the anchor points of
# the curves in Leo's figure (x: 2013 at 80, 94.6 per year; y: 1.1M at 180 above the axis at 318).
LEO_ML3 = [(510, 318), (581, 309), (636, 302), (683, 293), (730, 285), (794, 269), (841, 244),
           (936, 195), (1014, 154), (1078, 138)]
LEO_ML4 = [(872, 318), (983, 314), (1023, 302), (1038, 261), (1046, 236), (1061, 187),
           (1078, 138)]
MATHLIB_2026 = (2026 + 5 / 12, 2.2)


def from_leo(points):
    return [(2013 + (x - 80) / 94.6, (318 - y) / 180 * 1.1) for x, y in points]


def x_of_year(year):
    return X0 + (year - FIRST_YEAR) * YEAR_W


def x_of(year, month):
    frac = 0.5 if month is None else (month - 0.5) / 12
    return x_of_year(year + frac)


def y_of_value(value):
    return AXIS_Y - value / MATHLIB_MAX * CURVE_H


def smooth_path(points):
    """A path through `points` with horizontal tangents, as in Leo's figure."""
    (x, y), rest = points[0], points[1:]
    d = f"M {x:.0f} {y:.0f}"
    for x1, y1 in rest:
        mx = (x + x1) / 2
        d += f" C {mx:.0f} {y:.0f} {mx:.0f} {y1:.0f} {x1:.0f} {y1:.0f}"
        x, y = x1, y1
    return d


def curve(name, color, data, opacity):
    pts = [(x_of_year(t), y_of_value(v)) for t, v in data]
    line = smooth_path(pts)
    area = f"{line} L {pts[-1][0]:.0f} {AXIS_Y - 2} L {pts[0][0]:.0f} {AXIS_Y - 2} Z"
    return [
        f'<path d="{area}" fill="url(#{name})"/>',
        f'<path d="{line}" fill="none" stroke="{color}" stroke-width="2" opacity="{opacity}"/>',
    ]


def assign_lanes(xs):
    """Greedily place each event in the first lane where its box and connector are free.

    A box may be shifted sideways from its marker by up to MAX_SHIFT; the connector stays vertical
    and still meets the box. Returns (lane index, box center) for each event.
    """
    placed = []  # (marker x, box center, lane index)

    def free(x, c, lane):
        dist, above = LANES[lane]
        if c - BOX_W / 2 < 2 or c + BOX_W / 2 > WIDTH - 2:
            return False
        for x2, c2, lane2 in placed:
            dist2, above2 = LANES[lane2]
            if above2 != above:
                continue
            if lane2 == lane and abs(c - c2) < BOX_W + GAP:
                return False
            # Connectors to farther lanes must not cross boxes in nearer lanes.
            if dist2 < dist and abs(x - c2) < BOX_W / 2 + GAP:
                return False
            if dist2 > dist and abs(x2 - c) < BOX_W / 2 + GAP:
                return False
        return True

    shifts = range(-MAX_SHIFT, MAX_SHIFT + 1)
    budget = [200000]

    def options(x):
        """For each lane: the smallest feasible shift and the leftmost feasible shift."""
        result = []
        for lane in range(len(LANES)):
            ok = [d for d in shifts if free(x, x + d, lane)]
            if ok:
                for d in {min(ok, key=abs), ok[0]}:
                    result.append((abs(d) + 20 * (lane // 2), lane, d))
        return sorted(result)

    def search(k):
        if k == len(xs):
            return True
        x = xs[k]
        for _, lane, d in options(x):
            budget[0] -= 1
            if budget[0] < 0:
                return False
            placed.append((x, x + d, lane))
            if search(k + 1):
                return True
            placed.pop()
        return False

    if not search(0):
        raise SystemExit("no layout found; remove events or enlarge the figure")
    return [(lane, c) for _, c, lane in placed]


def svg():
    end = x_of_year(LAST_YEAR + 1) + 10
    out = [
        f'<svg viewBox="0 0 {WIDTH} {HEIGHT}" xmlns="http://www.w3.org/2000/svg" role="img" '
        'font-family="Source Sans 3, sans-serif">',
        '<defs>'
        '<linearGradient id="ml3grad" x1="0" y1="0" x2="0" y2="1">'
        '<stop offset="0%" stop-color="#0891b2" stop-opacity="0.12"/>'
        '<stop offset="100%" stop-color="#0891b2" stop-opacity="0.02"/></linearGradient>'
        '<linearGradient id="ml4grad" x1="0" y1="0" x2="0" y2="1">'
        '<stop offset="0%" stop-color="#dc2626" stop-opacity="0.14"/>'
        '<stop offset="100%" stop-color="#dc2626" stop-opacity="0.03"/></linearGradient>'
        '</defs>',
    ]

    # Mathlib curves: Mathlib 3 until the port, then Mathlib 4 (interpolated after July 2023).
    ml3, ml4 = from_leo(LEO_ML3), from_leo(LEO_ML4)
    out += curve("ml3grad", "#0891b2", ml3, 0.4)
    out += curve("ml4grad", "#dc2626", ml4 + [MATHLIB_2026], 0.5)
    (t0, v0), (t1, v1) = ml4[-1], MATHLIB_2026
    x1, y1 = x_of_year(t1), y_of_value(v1)
    out.append(f'<circle cx="{x1:.0f}" cy="{y1:.0f}" r="3.5" fill="#dc2626" opacity="0.6"/>')
    out.append(f'<text x="{x1:.0f}" y="{y1 - 12:.0f}" text-anchor="middle" font-size="13" '
               'fill="#64748b">2.2M</text>')
    # The legend goes to the top left; its y coordinates are filled in after cropping.
    for i, (label, color) in enumerate([("Mathlib 3 lines of code", "#0891b2"),
                                        ("Mathlib 4 lines of code", "#dc2626")]):
        out.append(f'<rect x="{X0}" y="LEGEND_Y{i}" width="18" height="4" rx="2" '
                   f'fill="{color}" opacity="0.7"/>')
        out.append(f'<text x="{X0 + 26}" y="LEGEND_T{i}" font-size="14" fill="#64748b">'
                   f'{label}</text>')

    # Axis.
    out.append(f'<line x1="{X0 - 30}" y1="{AXIS_Y}" x2="{end}" y2="{AXIS_Y}" stroke="#0891b2" '
               'stroke-width="3"/>')
    out.append(f'<polygon points="{end},{AXIS_Y - 7} {end + 18},{AXIS_Y} {end},{AXIS_Y + 7}" '
               'fill="#0891b2"/>')
    for year in range(FIRST_YEAR, LAST_YEAR + 1):
        x = x_of_year(year)
        out.append(f'<line x1="{x}" y1="{AXIS_Y - 6}" x2="{x}" y2="{AXIS_Y + 6}" '
                   'stroke="#0891b2" stroke-width="2"/>')
        out.append(f'<text x="{x}" y="{AXIS_Y + 30}" text-anchor="middle" font-size="15" '
                   f'fill="#64748b">{year}</text>')

    # Events. Connectors first, so that markers and boxes are drawn on top of them.
    events = sorted(EVENTS, key=lambda e: x_of(e[2], e[3]))
    xs = [round(x_of(e[2], e[3])) for e in events]
    spots = assign_lanes(xs)
    boxes, markers = [], []
    for (title, date, _, _, hi), x, (lane, c) in zip(events, xs, spots):
        dist, above = LANES[lane]
        top = AXIS_Y - dist - BOX_H if above else AXIS_Y + dist
        y2 = top + BOX_H if above else top
        out.append(f'<line x1="{x}" y1="{AXIS_Y}" x2="{x}" y2="{y2}" '
                   f'stroke="{"#94a3b8" if hi else "#cbd5e1"}" stroke-width="1.5"/>')
        if hi:
            markers.append(f'<circle cx="{x}" cy="{AXIS_Y}" r="8" fill="#0073A3"/>')
            box = 'fill="#fff" stroke="#0073A3" stroke-width="2"'
            fill, weight = "#0073A3", 700
        else:
            markers.append(f'<circle cx="{x}" cy="{AXIS_Y}" r="5" fill="#fff" stroke="#0891b2" '
                           'stroke-width="2.5"/>')
            box = 'fill="#f8fafc" stroke="#e2e8f0"'
            fill, weight = "#0f172a", 600
        boxes.append(f'<rect x="{c - BOX_W // 2}" y="{top}" width="{BOX_W}" height="{BOX_H}" '
                     f'rx="8" {box}/>')
        boxes.append(f'<text x="{c}" y="{top + 22}" text-anchor="middle" font-size="16" '
                     f'font-weight="{weight}" fill="{fill}">{title.replace("&", "&amp;")}</text>')
        boxes.append(f'<text x="{c}" y="{top + 41}" text-anchor="middle" font-size="13" '
                     f'fill="#64748b">{date}</text>')
    out += markers + boxes
    out.append("</svg>")
    # Crop vertically to the content: the legend above the highest box or curve point, and the
    # lowest box below.
    tops = [AXIS_Y - LANES[lane][0] - BOX_H for lane, _ in spots if LANES[lane][1]]
    bottoms = [AXIS_Y + LANES[lane][0] + BOX_H for lane, _ in spots if not LANES[lane][1]]
    y_min = min(tops + [y_of_value(MATHLIB_MAX) - 20, AXIS_Y - 60]) - 70
    y_max = max(bottoms + [AXIS_Y + 40]) + 10
    out[0] = out[0].replace(f'viewBox="0 0 {WIDTH} {HEIGHT}"',
                            f'viewBox="0 {y_min:.0f} {WIDTH} {y_max - y_min:.0f}"')
    legend_y = y_min + 30
    return "\n".join(out).replace("LEGEND_Y0", f"{legend_y - 6:.0f}").replace(
        "LEGEND_Y1", f"{legend_y + 16:.0f}").replace("LEGEND_T0", f"{legend_y:.0f}").replace(
        "LEGEND_T1", f"{legend_y + 22:.0f}") + "\n"


if __name__ == "__main__":
    Path("static/images/math-timeline.svg").write_text(svg())
