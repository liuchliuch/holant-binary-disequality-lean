import Holant.Proofs.Hardness.GeneralOddResidueMinimal
import Mathlib.Algebra.GCDMonoid.Finset

/-! The signed support lattice is computed from the original finite tables.
The primitive-lattice case now produces an actual original ordinary unary,
with the already proved original-field controlled installation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddResidueGcd
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction SupportDescent SupportCaps
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open GeneralOddUnaryOrdinary GeneralOddUnarySource
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))

/-- Zero entries make no contribution. Positive and negative charges are both
included, across all original rows and every word in their exact tables. -/
def supportGcd : ℕ := by
  classical
  exact Finset.univ.gcd (fun p : (k : Fin s) × (Fin (a k.val)→Bool) =>
    if sourceKBasis.symm.action (G p.1) p.2≠0 then (balance true p.2).natAbs else 0)

/-- An exact finite-gcd characterization; there is no closure or graph premise. -/
theorem dvd_supportGcd_iff (d : ℕ) : d∣supportGcd G ↔
    ∀ k : Fin s,∀ x : Fin (a k.val)→Bool,
      sourceKBasis.symm.action (G k) x≠0 → (d : ℤ)∣balance true x := by
  classical
  unfold supportGcd
  rw [Finset.dvd_gcd_iff]
  constructor
  · intro h k x hx
    have hd := h ⟨k,x⟩ (Finset.mem_univ _)
    change d∣(if sourceKBasis.symm.action (G k) x≠0 then (balance true x).natAbs else 0) at hd
    rw [ite_eq_left hx] at hd
    exact Int.natCast_dvd.mpr hd
  · intro h p _
    by_cases hp : sourceKBasis.symm.action (G p.1) p.2≠0
    · change d∣(if sourceKBasis.symm.action (G p.1) p.2≠0 then (balance true p.2).natAbs else 0)
      rw [ite_eq_left hp]
      exact Int.natCast_dvd.mp (h p.1 p.2 hp)
    · change d∣(if sourceKBasis.symm.action (G p.1) p.2≠0 then (balance true p.2).natAbs else 0)
      rw [ite_eq_right hp]
      exact dvd_zero _

/-- The minimal odd arity divides the computed original signed support gcd. -/
theorem minimal_dvd_supportGcd (D : GeneralOddMinimalTerminal.Minimal G)
    (hside : ¬CommonOneSided (kCoordinates (original G))) : D.arity∣supportGcd G := by
  by_cases h1 : D.arity=1
  · rw [h1]; exact one_dvd _
  · have hh : 3≤D.arity := by obtain ⟨k,hk⟩ := D.odd; omega
    apply (dvd_supportGcd_iff G D.arity).mpr
    exact GeneralOddResidueMinimal.all_balance_divisible G D hh hside

/-- Primitive original support charges force the actual minimal odd graph to
have arity one. No unary graph or tensor-factor witness is supplied. -/
theorem minimal_unary (D : GeneralOddMinimalTerminal.Minimal G)
    (hside : ¬CommonOneSided (kCoordinates (original G)))
    (hprimitive : supportGcd G=1) : D.arity=1 := by
  have hd := minimal_dvd_supportGcd G D hside
  rw [hprimitive] at hd
  exact Nat.dvd_one.mp hd

/-- Actual unary extraction from an original nonzero odd row, both support
signs, and the computable primitive-charge condition on the original tables. -/
theorem source_unary (j : Fin s) (ho : Odd (a j.val)) (hnz : G j≠0)
    (hside : ¬CommonOneSided (kCoordinates (original G)))
    (hprimitive : supportGcd G=1) :
    ∃ U : GeneralOddHighTerminalAccess.Actual G 1,U.graph.denote≠0 ∧
      Nonempty (GeneralOddHighTerminalAccess.Reduction G U) := by
  let D := GeneralOddMinimalTerminal.select G j ho hnz
  have hd : D.arity=1 := minimal_unary G D hside hprimitive
  let N := reboundary D.graph (finCongr hd)
  have hN : N.denote≠0 := by
    intro hz
    apply D.nonzero
    funext x
    have he := congrFun hz (fun i=>x ((finCongr hd).symm i))
    simpa only [N,reboundary_denote,Equiv.symm_apply_apply,Pi.zero_apply] using he
  exact ⟨⟨N,D.uses,D.ordinary⟩,hN,⟨GeneralOddHighTerminalAccess.controlled G _⟩⟩

/-- Under the primitive-charge condition, the negative original-input problem
has an actual unary or the literal one-sided EO failure. -/
theorem source (j : Fin s) (ho : Odd (a j.val)) (hnz : G j≠0)
    (hnot : ¬Tract (original G)) (hprimitive : supportGcd G=1) :
    (CommonOneSided (kCoordinates (preprocess (original G))) ∧
      ¬EOTract (centralFamily (kCoordinates (preprocess (original G))))) ∨
    (∃ U : GeneralOddHighTerminalAccess.Actual G 1,U.graph.denote≠0 ∧
      Nonempty (GeneralOddHighTerminalAccess.Reduction G U)) := by
  by_cases hside : CommonOneSided (kCoordinates (preprocess (original G)))
  · exact .inl ⟨hside,oneSided_eo_failure G hnot hside⟩
  · apply Or.inr
    apply source_unary G j ho hnz _ hprimitive
    intro h
    apply hside
    exact h.mono_family (Set.image_mono (fun _ h=>h.1))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddResidueGcd
