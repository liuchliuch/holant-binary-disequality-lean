import Holant.Proofs.Closure.OccurrenceCurrent
import Holant.Proofs.Closure.RetainedFinalAccess

/-! Exponent-one access at an exact retained integer label. No choice among
other labels of the same table is made. The single original root occurrence,
its port order and its literal label are installed in the actual macro. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedDeckTransport
open Holant Holant.Complexity Holant.Tractable
open Holant.Complexity.FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.GeneralExtraction
variable {L : Type*} [Field L] {s : ℕ} {a : ℕ → ℕ}
variable (T : (i : Fin s) → Signature L (a i.val)) (j : Fin s)

/-- Exactly one vertex with the saved integer root label j. -/
def labelNetwork : Network L (1 * a j.val) where
  shape := {
    vertices := 1
    arity := fun _ => a j.val
    edges := 0
    ports := {
      toFun p := .inl (finProdFinEquiv (p.1,p.2))
      invFun q := Sum.elim (fun i => ⟨(finProdFinEquiv.symm i).1,(finProdFinEquiv.symm i).2⟩)
        (fun p => Fin.elim0 p.1) q
      left_inv := by
        rintro ⟨v,i⟩
        have he : (finProdFinEquiv.symm (finProdFinEquiv (v,i)) : Fin 1 × Fin (a j.val)) = (v,i) :=
          Equiv.symm_apply_apply finProdFinEquiv (v,i)
        change (⟨(finProdFinEquiv.symm (finProdFinEquiv (v,i))).1,
          (finProdFinEquiv.symm (finProdFinEquiv (v,i))).2⟩ : Σ _v : Fin 1, Fin (a j.val)) = ⟨v,i⟩
        rw [he]
      right_inv := by intro q; cases q with
        | inl i =>
            change Sum.inl (finProdFinEquiv (finProdFinEquiv.symm i)) = Sum.inl i
            exact congrArg Sum.inl (Equiv.apply_symm_apply finProdFinEquiv i)
        | inr p => exact Fin.elim0 p.1 } }
  vertex := fun _ => T j
  edge := fun e => Fin.elim0 e

def labelLabelling : Labelling (labelNetwork T j).shape s 1 a where
  vertex := fun _ => j
  vertex_arity := fun _ => rfl
  edge := fun e => Fin.elim0 e

def labelPower : GeneralPowerExposure.PowerMacro T (T j) where
  exponent := 1
  positive := by omega
  scale := 1
  scale_ne_zero := one_ne_zero
  network := labelNetwork T j
  labels := labelLabelling T j
  value := by
    rw [Labelling.denote_template_of_labels (labelLabelling T j) T (fun _ => Signature.disequality)
      (labelNetwork T j).vertex (labelNetwork T j).edge]
    · funext x
      simp [Network.denote,labelNetwork,Carrier.blockPower]
      change (∑ z : (Fin 0 × Bool) → Bool,
        (∏ v : Fin 1, T j (fun i => x (finProdFinEquiv (v,i)))) *
          ∏ e : Fin 0, (Fin.elim0 e : Bool → Bool → L) (z (e,false)) (z (e,true))) =
        T j (fun i => x (finProdFinEquiv (0,i)))
      simp
    · intro v x
      rfl
    · intro e
      exact Fin.elim0 e

theorem labelPower_exact_label (v : Fin (labelPower T j).network.shape.vertices) :
    (labelPower T j).labels.vertex v = j := rfl

def castAnyPower {q r : AnySignature L}
    (literal : q = r) (M : GeneralPowerExposure.PowerMacro T q.2) :
    GeneralPowerExposure.PowerMacro T r.2 := literal ▸ M

theorem castAnyPower_network {q r : AnySignature L}
    (literal : q = r) (M : GeneralPowerExposure.PowerMacro T q.2) :
    HEq (castAnyPower T literal M).network M.network := by
  cases literal
  rfl

theorem castAnyPower_labels {q r : AnySignature L}
    (literal : q = r) (M : GeneralPowerExposure.PowerMacro T q.2) (label : Fin s)
    (actual : ∀ v, M.labels.vertex v = label) :
    ∀ v, (castAnyPower T literal M).labels.vertex v = label := by
  cases literal
  exact actual

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedDeckTransport
end
