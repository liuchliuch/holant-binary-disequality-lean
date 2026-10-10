import Holant.Certificates.NormalizedDihedralQ6.Projection
import Holant.Tensor
import Mathlib.Data.Finset.Sort

/-! Original-port coordinates for the physical six-to-four contraction.
The remaining ports retain increasing original order. No port is pinned. -/
namespace Holant.Certificates.NormalizedDihedralQ6

set_option backward.isDefEq.respectTransparency false

def remainingSet (p : Pair) : Finset Port := Finset.univ.filter (fun i => i ≠ p.1 ∧ i ≠ p.2)

theorem remainingSet_card (p : Pair) (hp : p.1 ≠ p.2) : (remainingSet p).card = 4 := by
  have h := remaining_card p hp
  simpa only [Remaining,Fintype.card_subtype,remainingSet] using h

def remainingSetEquiv (p : Pair) : ↥(remainingSet p) ≃ Remaining p :=
  Equiv.subtypeEquivRight (fun i => by simp [remainingSet])

/-- The four surviving ports, in increasing original order. -/
def remainingEquiv (p : Pair) (hp : p.1 ≠ p.2) : Fin 4 ≃ Remaining p :=
  ((remainingSet p).orderIsoOfFin (remainingSet_card p hp)).toEquiv.trans (remainingSetEquiv p)

theorem remainingEquiv_strictMono (p : Pair) (hp : p.1 ≠ p.2) :
    StrictMono (fun i : Fin 4 => (remainingEquiv p hp i).val) := by
  intro i j hij
  exact ((remainingSet p).orderIsoOfFin (remainingSet_card p hp)).strictMono hij

def orderedPorts (p : Pair) (hp : p.1 ≠ p.2) : Equiv.Perm Port where
  toFun := Fin.cases p.1 (Fin.cases p.2 (fun i => (remainingEquiv p hp i).val))
  invFun i := if h : i = p.1 then 0 else if h' : i = p.2 then 1
    else ((remainingEquiv p hp).symm ⟨i,h,h'⟩).succ.succ
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => ?_) j
      · change (if h : p.2 = p.1 then (0 : Port) else if h' : p.2 = p.2 then 1 else ((remainingEquiv p hp).symm ⟨p.2,h,h'⟩).succ.succ) = 1
        simp [Ne.symm hp]
      · simp [(remainingEquiv p hp k).property.1,(remainingEquiv p hp k).property.2]
  right_inv i := by
    dsimp only
    split_ifs with h h'
    · subst i; rfl
    · subst i; rfl
    · simp

@[simp] theorem orderedPorts_zero (p : Pair) (hp : p.1 ≠ p.2) : orderedPorts p hp 0 = p.1 := rfl
@[simp] theorem orderedPorts_one (p : Pair) (hp : p.1 ≠ p.2) : orderedPorts p hp 1 = p.2 := rfl
@[simp] theorem orderedPorts_remaining (p : Pair) (hp : p.1 ≠ p.2) (i : Fin 4) :
    orderedPorts p hp i.succ.succ = (remainingEquiv p hp i).val := rfl

/-- The original six-port word for a choice of the two internal endpoint bits. -/
def joinWord (p : Pair) (hp : p.1 ≠ p.2) (a b : Bool) (x : Fin 4 → Bool) : Word :=
  fun i => (Fin.cons a (Fin.cons b x) : Fin 6 → Bool) ((orderedPorts p hp).symm i)

def externalWord (p : Pair) (hp : p.1 ≠ p.2) (x : Word) : Fin 4 → Bool :=
  fun i => x (remainingEquiv p hp i).val

@[simp] theorem joinWord_first (p : Pair) (hp : p.1 ≠ p.2) (a b : Bool) (x : Fin 4 → Bool) :
    joinWord p hp a b x p.1 = a := by
  change (Fin.cons a (Fin.cons b x) : Fin 6 → Bool) ((orderedPorts p hp).symm (orderedPorts p hp 0)) = a
  simp only [Equiv.symm_apply_apply,Fin.cons_zero]
@[simp] theorem joinWord_second (p : Pair) (hp : p.1 ≠ p.2) (a b : Bool) (x : Fin 4 → Bool) :
    joinWord p hp a b x p.2 = b := by
  change (Fin.cons a (Fin.cons b x) : Fin 6 → Bool) ((orderedPorts p hp).symm (orderedPorts p hp 1)) = b
  simp only [Equiv.symm_apply_apply,Fin.cons_one,Fin.cons_zero]
@[simp] theorem external_joinWord (p : Pair) (hp : p.1 ≠ p.2) (a b : Bool) (x : Fin 4 → Bool) :
    externalWord p hp (joinWord p hp a b x) = x := by
  funext i
  change (Fin.cons a (Fin.cons b x) : Fin 6 → Bool) ((orderedPorts p hp).symm (orderedPorts p hp i.succ.succ)) = x i
  simp only [Equiv.symm_apply_apply,Fin.cons_succ]

theorem joinWord_external (p : Pair) (hp : p.1 ≠ p.2) (x : Word) :
    joinWord p hp (x p.1) (x p.2) (externalWord p hp x) = x := by
  funext i
  obtain ⟨j,rfl⟩ := (orderedPorts p hp).surjective i
  simp only [joinWord,Equiv.symm_apply_apply]
  refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · rfl

theorem external_eq_iff_restrict_eq (p : Pair) (hp : p.1 ≠ p.2) (x y : Word) :
    externalWord p hp x = externalWord p hp y ↔ restrict p x = restrict p y := by
  constructor
  · intro h
    funext i
    obtain ⟨j,rfl⟩ := (remainingEquiv p hp).surjective i
    exact congrFun h j
  · intro h
    funext i
    exact congrFun h (remainingEquiv p hp i)

theorem external_eq_iff_project_eq (p : Pair) (hp : p.1 ≠ p.2) (x y : Word) :
    externalWord p hp x = externalWord p hp y ↔ project p x = project p y :=
  (external_eq_iff_restrict_eq p hp x y).trans (project_eq_iff_restrict_eq p x y).symm

/-- The actual ordered four-port image has the same cardinality as the A.9 projected set. -/
theorem external_image_card (S : Support) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool) :
    ((slice S p γ).image (externalWord p hp)).card = (projected S p γ).card := by
  have he : Function.Injective (fun x : Remaining p → Bool => fun i : Fin 4 => x (remainingEquiv p hp i)) := by
    intro x y h
    funext i
    obtain ⟨j,rfl⟩ := (remainingEquiv p hp).surjective i
    exact congrFun h j
  have hc := Finset.card_image_of_injective ((slice S p γ).image (restrict p)) he
  rw [Finset.image_image] at hc
  change ((slice S p γ).image (externalWord p hp)).card = _ at hc
  exact hc.trans (projected_card_restriction S p γ).symm

end Holant.Certificates.NormalizedDihedralQ6
