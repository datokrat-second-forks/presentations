# Instance Assignment Failures

This Verso deck presents ten instance-assignment failure modes from the Mathlib RT/EIT experiment.

The project uses these local builds:

- Lean: `/root/lean4/julia-minimal/build/release/stage1`
- Mathlib: `/root/mathlib4/julia-minimal`

Build and render the deck:

```bash
lake update
./prepare-dependencies.sh
lake build
lake env lean --run Main.lean
```

The preparation script applies two compatibility patches. One avoids a `grind` regression in
Verso's Z85 encoder. The other preserves dependency paths when Verso extracts isolated modules.

The rendered deck is in `_slides/index.html`.
