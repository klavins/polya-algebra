import PolyaAlgebra.GroupTheory
-- Every declaration of `GroupTheory` that `to_additive` has paired with an additive one, as
-- `multiplicative additive` lines: the names the explicit `@[to_additive NAME]` marks write.
open Lean Elab Command Mathlib.Tactic in
run_cmd do
  let env ← getEnv
  let names := env.constants.fold (fun acc n _ => acc.push n) (#[] : Array Name)
  for n in names do
    if (`GroupTheory).isPrefixOf n then
      if let some a := Translate.findTranslationName? env ToAdditive.data n then
        IO.println s!"{n} {a}"
