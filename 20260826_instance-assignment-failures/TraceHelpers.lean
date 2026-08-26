module

public import Lean.PostprocessTraces
public import Lean.CoreM
public import Lean.Message

open Lean PostprocessTraces

public partial def elideBelow (p : TracePattern) : TracePostprocessor := fun trees =>
  trees.mapM go
where
  go (t : TraceTree) : CoreM TraceTree := do
    match t with
    | .leaf msg => return .leaf msg
    | .node data msg children wrap =>
      if ← p t then
        return .node data m!"{msg} (truncated)" #[] wrap
      else
        return .node data msg (← children.mapM go) wrap

public partial def dropSubtrees (p : TracePattern) : TracePostprocessor := fun trees =>
  trees.filterMapM go
where
  go (t : TraceTree) : CoreM (Option TraceTree) := do
    if ← p t then return none
    match t with
    | .leaf msg => return some (.leaf msg)
    | .node data msg children wrap =>
      return some (.node data msg (← children.filterMapM go) wrap)
