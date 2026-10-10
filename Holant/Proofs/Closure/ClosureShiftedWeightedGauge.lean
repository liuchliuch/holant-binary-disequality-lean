import Holant.Proofs.Closure.ClosureShiftedWeightedObstruction
import Holant.Proofs.Closure.ClosureShiftedWeightedCards
import Holant.Proofs.Closure.ClosureProgramStability
import Holant.Marked.WeightedGauge.Basic

/-! One coherent port gauge for literal weighted products sharing an actual
unordered pairing. Its inverse and exact ordered presentations are explicit.
CURRENT source mate equality will be used only above the six-port boundary. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.MatchingContractionClosure
open Holant.Dihedral.TwoCardLocalization
open scoped BigOperators
abbrev D (d : Scalar) : Mat := diagonalKernel 1 d

private theorem diagonal_inverse (d : Scalar) (hd : d ≠ 0) :
    Kernel.mul (D d) (D d⁻¹) = Signature.equality := by
  funext a b
  cases a <;> cases b <;> simp [D,diagonalKernel,Kernel.mul_apply,hd,Signature.equality]

/-- Squared-root condition, derived in shifted A, makes diagonal conjugacy
preserve the standard group even though the diagonal itself is outside it. -/
theorem diagonal_conjugate_mem {m : ℕ} (d : Scalar) (hd : d ≠ 0) (hr : Roots m (d^2))
    (T : Mat) (member : T ∈ groupM m) :
    Kernel.mul (Kernel.mul (D d) T) (D d⁻¹) ∈ groupM m := by
  obtain ⟨t,ht,h | h⟩ := member
  · obtain ⟨c,hc,rfl⟩ := h
    rw [scale_mul_right,scale_mul_left]
    refine ⟨t,ht,Or.inl ⟨c,hc,?_⟩⟩
    congr 1
    funext a b
    cases a <;> cases b <;> simp [D,R,diagonalKernel,Kernel.mul_apply,hd] <;> field_simp
  · obtain ⟨c,hc,rfl⟩ := h
    rw [scale_mul_right,scale_mul_left]
    refine ⟨t/(d^2),ht.div hr,Or.inr ⟨c*d,mul_ne_zero hc hd,?_⟩⟩
    funext a b
    cases a <;> cases b <;> simp [D,R,S,scale,diagonalKernel,Kernel.mul_apply,Signature.disequality] <;>
      field_simp [hd] <;> ring

/-- Either orientation of the SAME weighted pair can receive the gauge weight. -/
theorem left_factor_mem {m : ℕ} (d : Scalar) (hd : d ≠ 0) (hr : Roots m (d^2))
    (B : Mat) (member : Kernel.mul B (D d) ∈ groupM m) :
    Kernel.mul (D d) B ∈ groupM m := by
  have h := diagonal_conjugate_mem d hd hr (Kernel.mul B (D d)) member
  have he : Kernel.mul (Kernel.mul (D d) (Kernel.mul B (D d))) (D d⁻¹) =
      Kernel.mul (D d) B := by
    rw [Kernel.mul_assoc,Kernel.mul_assoc,diagonal_inverse d hd,Kernel.mul_equality]
  rwa [he] at h

variable {n : ℕ}

def rightWeights (M : Presentation Scalar (Fin n)) (d : Scalar) : Fin n → Scalar :=
  fun j => if (M.ports.symm j).2 then d else 1

theorem rightWeights_nonzero (M : Presentation Scalar (Fin n)) (d : Scalar) (hd : d ≠ 0) :
    ∀ j, rightWeights M d j ≠ 0 := by
  intro j
  unfold rightWeights
  split
  · exact hd
  · exact one_ne_zero

def gaugePresentation (M : Presentation Scalar (Fin n)) (r : Fin n → Scalar) :
    Presentation Scalar (Fin n) where
  edges := M.edges
  ports := M.ports
  matrix e := Matrix.of (Kernel.mul
    (Kernel.mul (WeightedGauge.diagonal (r (M.ports (e,false)))) (M.matrix e))
    (WeightedGauge.diagonal (r (M.ports (e,true)))))
  scalar := M.scalar

@[simp] theorem gaugePresentation_ports (M : Presentation Scalar (Fin n)) (r : Fin n → Scalar) :
    (gaugePresentation M r).ports = M.ports := rfl
@[simp] theorem gaugePresentation_scalar (M : Presentation Scalar (Fin n)) (r : Fin n → Scalar) :
    (gaugePresentation M r).scalar = M.scalar := rfl

/-- Exact finite product transport at the recorded ordered matching. -/
theorem gaugePresentation_tensor (M : Presentation Scalar (Fin n)) (r : Fin n → Scalar) :
    WeightedGauge.gauge r M.tensor = (gaugePresentation M r).tensor := by
  funext x
  change (∏ j,WeightedGauge.bitWeight (r j) (x j)) *
      (M.scalar * ∏ e,M.matrix e (x (M.ports (e,false))) (x (M.ports (e,true)))) = _
  rw [←M.ports.prod_comp (fun j => WeightedGauge.bitWeight (r j) (x j)),Fintype.prod_prod_type]
  simp only [Fintype.prod_bool]
  change (∏ e,WeightedGauge.bitWeight (r (M.ports (e,true))) (x (M.ports (e,true))) *
      WeightedGauge.bitWeight (r (M.ports (e,false))) (x (M.ports (e,false)))) *
      (M.scalar * ∏ e,M.matrix e (x (M.ports (e,false))) (x (M.ports (e,true)))) = _
  rw [mul_left_comm _ M.scalar,←Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  simp only [gaugePresentation,Matrix.of_apply,WeightedGauge.diagonal_mul,WeightedGauge.mul_diagonal]
  ring

/-- Pairing equality supplies the common gauge's two actual endpoint weights. -/
theorem rightWeights_same_pairing (M N : Presentation Scalar (Fin n)) (d : Scalar)
    (same : (presentationMatching M).mate = (presentationMatching N).mate) (e : Fin N.edges) :
    (rightWeights M d (N.ports (e,false)) = 1 ∧ rightWeights M d (N.ports (e,true)) = d) ∨
    (rightWeights M d (N.ports (e,false)) = d ∧ rightWeights M d (N.ports (e,true)) = 1) := by
  obtain ⟨⟨i,b⟩,hi⟩ := M.ports.surjective (N.ports (e,false))
  have hmate := congrArg (fun mate : Equiv.Perm (Fin n) => mate (N.ports (e,false))) same
  have hopposite : N.ports (e,true) = M.ports (i,!b) := by
    have hl : (presentationMatching M).mate (N.ports (e,false)) = M.ports (i,!b) := by
      rw [←hi]
      exact Holant.Pauli.ExoticKlein.Matching.mate_port (presentationMatching M) i b
    have hr : (presentationMatching N).mate (N.ports (e,false)) = N.ports (e,true) :=
      Holant.Pauli.ExoticKlein.Matching.mate_port (presentationMatching N) e false
    rw [hl,hr] at hmate
    exact hmate.symm
  rw [←hi,hopposite]
  cases b <;> simp [rightWeights]

/-- Reversed edge orientation is covered by the actual squared-phase root. -/
theorem shared_gauge_factors {m : ℕ} (d : Scalar) (hd : d ≠ 0) (hr : Roots m (d^2))
    (M N : Presentation Scalar (Fin n))
    (same : (presentationMatching M).mate = (presentationMatching N).mate)
    (weighted : ∀ e,Kernel.mul (N.matrix e) (D d) ∈ groupM m) :
    ∀ e,(gaugePresentation N (rightWeights M d)).matrix e ∈ groupM m := by
  intro e
  have diag (z : Scalar) : WeightedGauge.diagonal z = D z := rfl
  have one : D 1 = Signature.equality := R_one
  rcases rightWeights_same_pairing M N d same e with h | h
  · change Kernel.mul (Kernel.mul (WeightedGauge.diagonal _) _) (WeightedGauge.diagonal _) ∈ groupM m
    rw [h.1,h.2,diag,diag,one,Kernel.equality_mul]
    exact weighted e
  · change Kernel.mul (Kernel.mul (WeightedGauge.diagonal _) _) (WeightedGauge.diagonal _) ∈ groupM m
    rw [h.1,h.2,diag,diag,one,Kernel.mul_equality]
    exact left_factor_mem d hd hr _ (weighted e)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
