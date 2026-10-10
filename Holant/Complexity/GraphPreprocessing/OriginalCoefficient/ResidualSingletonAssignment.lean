import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingletonSpec

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingleton
open Computability
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

private theorem ports_eq (r : RawClosedNetwork) (p q : r.Ports arity)
    (hv : p.1=q.1) (hi : p.2.val=q.2.val) : p=q := by
  rcases p with ⟨v,i⟩
  rcases q with ⟨w,j⟩
  dsimp only at hv hi
  cases hv
  have he : i=j := Fin.ext hi
  cases he
  rfl

/-- The dynamically looked-up surviving position is exactly its original
edge/end occurrence, including its original local-port coordinate. -/
theorem survivor_eq_some (x : Input s b arity)
    (j : Fin (arity (x.val.1.val.vertices.get x.val.2.1).1)) :
    ResidualSurvivorQuery.selected (survivorQuery x) = some j ↔
      x.val.1.val.route x.val.1.property ⟨x.val.2.1,j⟩ = x.val.2.2.2 := by
  change (ResidualPin.selected true x.val.1.val x.val.2.1
    (x.val.1.val.lookup x.val.1.property x.val.2.2.2)).map Prod.fst = some j ↔ _
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨p,hp,hpj⟩
    obtain ⟨hv,hi,_⟩ := ResidualPin.selected_some true x.val.1.val x.val.2.1 _ p hp
    have he := ports_eq x.val.1.val (x.val.1.val.lookup x.val.1.property x.val.2.2.2)
      ⟨x.val.2.1,j⟩ hv (hi.trans (congrArg Fin.val hpj))
    rw [← he,x.val.1.val.route_lookup]
  · intro he
    have hp : x.val.1.val.lookup x.val.1.property x.val.2.2.2 = ⟨x.val.2.1,j⟩ := by
      apply (x.val.1.val.route_bijective x.val.1.property).1
      rw [x.val.1.val.route_lookup,he]
    rw [hp]
    exact ⟨(j,true),by simp [ResidualPin.selected],rfl⟩

def originalAssignment (a z : Bool) (x : Input s b arity)
    (j : Fin (arity (x.val.1.val.vertices.get x.val.2.1).1)) : Bool :=
  let q := x.val.1.val.route x.val.1.property ⟨x.val.2.1,j⟩
  if q.1=x.val.2.2.1 then if q.2 then z else a else decide (q=x.val.2.2.2)

/-- Exact original assignment: removed ports get their independent bits, the
surviving original occurrence gets one, and every other port gets zero. -/
theorem descriptor_assignment (a z : Bool) (x : Input s b arity) :
    ResidualLabel.assignment (descriptor a z x) = originalAssignment a z x := by
  funext j
  change ((ResidualLabel.pinAt (ResidualPin.selected a x.val.1.val x.val.2.1
      (x.val.1.val.lookup x.val.1.property (x.val.2.2.1,false))) j).orElse
    (fun _ => ResidualLabel.pinAt (ResidualPin.selected z x.val.1.val x.val.2.1
      (x.val.1.val.lookup x.val.1.property (x.val.2.2.1,true))) j)).getD
    (decide (ResidualSurvivorQuery.selected (survivorQuery x) = some j)) = _
  rw [ResidualPin.pinAt_lookup,ResidualPin.pinAt_lookup]
  simp only [survivor_eq_some]
  unfold originalAssignment
  generalize hq : x.val.1.val.route x.val.1.property ⟨x.val.2.1,j⟩ = q
  rcases q with ⟨f,side⟩
  cases side <;> by_cases hf : f=x.val.2.2.1 <;> simp [hf]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingleton
