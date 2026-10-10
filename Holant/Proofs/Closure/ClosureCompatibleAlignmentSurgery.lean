import Holant.Proofs.Closure.ClosureCompatibleAlignmentTags
import Holant.Proofs.Closure.ClosureCompatibleAlignmentObstruction

/-! Exact ordered deletion/splicing products for the one-step discrepancy
argument.  The residual ports are the actual undeleted original ports; no
new independently selected matching or factor tree is substituted. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Tractable Holant.Marked
open Holant.Dihedral.CompatibleCoefficientLine Holant.Dihedral.TwoCardLocalization
open Holant.LocalDrafts.FinitePGL2.Stabilization

namespace MC
export Holant.Certificates.MatchingContractionClosure
  (Binary Presentation productValue OtherEdges Remaining deletePorts splicePorts
    spliceFactors contractPair contract_matched contract_cross)
end MC

variable {n r : ℕ}

theorem port_distinct (p : (Fin r × Bool) ≃ Fin (n+2)) (e : Fin r) :
    p (e,false) ≠ p (e,true) := by
  intro equal
  have h := congrArg Prod.snd (p.injective equal)
  cases h

def deleteOrder (p : (Fin r × Bool) ≃ Fin (n+2)) (e : Fin r) : Equiv.Perm (Fin (n+2)) :=
  Holant.Dihedral.CompatibleClosure.pairOrder (p (e,false)) (p (e,true))

def deleteOutputPorts (p : (Fin r × Bool) ≃ Fin (n+2)) (e : Fin r) :
    (MC.OtherEdges e × Bool) ≃ Fin n :=
  (MC.deletePorts p e).trans (remainingOrder _ _ (port_distinct p e)).symm

set_option backward.isDefEq.respectTransparency false in
theorem ordered_delete_product (p : (Fin r × Bool) ≃ Fin (n+2))
    (A : Fin r → MC.Binary (K:=Scalar)) (κ : Scalar) (e : Fin r) (C : Mat) :
    Signature.contract C (Tensor.reindex (deleteOrder p e).symm (MC.productValue p A κ)) =
      MC.productValue (deleteOutputPorts p e) (fun j => A j.val)
        (Holant.Certificates.MatchingContractionClosure.trace (A e) C * κ) := by
  dsimp only [deleteOrder]
  rw [← contractPair_order _ _ (port_distinct p e) C]
  rw [MC.contract_matched]
  rfl

theorem cross_port_distinct (p : (Fin r × Bool) ≃ Fin (n+2))
    (e f : Fin r) (different : e ≠ f) : p (e,true) ≠ p (f,false) :=
  fun equal => different (congrArg Prod.fst (p.injective equal))

def spliceOrder (p : (Fin r × Bool) ≃ Fin (n+2)) (e f : Fin r) : Equiv.Perm (Fin (n+2)) :=
  Holant.Dihedral.CompatibleClosure.pairOrder (p (e,true)) (p (f,false))

def spliceOutputPorts (p : (Fin r × Bool) ≃ Fin (n+2))
    (e f : Fin r) (different : e ≠ f) : (MC.OtherEdges f × Bool) ≃ Fin n :=
  (MC.splicePorts p e f).trans (remainingOrder _ _ (cross_port_distinct p e f different)).symm

set_option backward.isDefEq.respectTransparency false in
theorem ordered_splice_product (p : (Fin r × Bool) ≃ Fin (n+2))
    (A : Fin r → MC.Binary (K:=Scalar)) (κ : Scalar)
    (e f : Fin r) (different : e ≠ f) (C : Mat) :
    Signature.contract C (Tensor.reindex (spliceOrder p e f).symm (MC.productValue p A κ)) =
      MC.productValue (spliceOutputPorts p e f different) (MC.spliceFactors C A e f) κ := by
  dsimp only [spliceOrder]
  rw [← contractPair_order _ _ (cross_port_distinct p e f different) C]
  rw [MC.contract_cross p A κ e f different]
  rfl

theorem generic_fuse_eq_marked (C A B : Mat) :
    Holant.Certificates.MatchingContractionClosure.fuse C A B = Holant.Marked.fuse C A B := by
  rw [Holant.Marked.fuse_eq_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem hasParity_det_nonzero {α : Bool} {A : Mat} (h : HasParity α A) : Matrix.det A ≠ 0 := by
  obtain ⟨w,nonzero,rfl⟩ := h
  rw [binary_det_formula]
  cases α <;> simp [monomial,nonzero]

theorem groupM_det_nonzero {m : ℕ} (positive : 0 < m) {A : Mat} (member : A ∈ groupM m) :
    Matrix.det A ≠ 0 := by
  obtain ⟨α,support⟩ := group_hasParity positive member
  exact hasParity_det_nonzero support

theorem group_product_nonzero {m : ℕ} (positive : 0 < m)
    {E : Type} [Fintype E] [DecidableEq E] {P : Type} [DecidableEq P]
    (p : (E × Bool) ≃ P) (A : E → MC.Binary (K:=Scalar)) (κ : Scalar)
    (member : ∀ e,A e ∈ groupM m) (nonzero : κ ≠ 0) : MC.productValue p A κ ≠ 0 :=
  Holant.Certificates.MatchingContractionClosure.productValue_nonzero p A κ
    (fun e => groupM_det_nonzero positive (member e)) nonzero

set_option backward.isDefEq.respectTransparency false in
theorem spliceFactors_member {m : ℕ} (positive : 0 < m)
    (A : Fin r → Mat) (e f : Fin r) (C : Mat)
    (member : ∀ j,A j ∈ groupM m) (connection : C ∈ groupM m) :
    ∀ j,MC.spliceFactors C A e f j ∈ groupM m := by
  intro j
  unfold Holant.Certificates.MatchingContractionClosure.spliceFactors
  split_ifs
  · rw [generic_fuse_eq_marked]
    exact Holant.Dihedral.CompatibleClosure.fuse_group_mem positive connection (member e) (member f)
  · exact member j.val

theorem projective_as_matrix_line (A B : Mat) :
    Holant.Marked.ProjectivelyEqual B A ↔ ∃ c : Scalar,c ≠ 0 ∧ B = c • A := Iff.rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
