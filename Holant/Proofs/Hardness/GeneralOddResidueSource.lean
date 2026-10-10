import Holant.Proofs.Hardness.GeneralOddResidueConservation

/-! Canonical original-input residue, after all actual odd-arity descents.
With both support signs, its arity is exactly the finite gcd of ALL supported
original charges. This makes the primitive unary case and the genuine
nonprimitive obstruction explicit, with original-field oracle access. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddResidueSource
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction SupportDescent SupportCaps
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open GeneralOddUnaryOrdinary GeneralOddUnarySource GeneralOddResidueGcd
open GeneralOddResidueConservation
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))

/-- An actual minimal graph realizes the canonical positive odd lattice
index. Its coefficients and all physical edges stay in the original family. -/
theorem source_exact (j : Fin s) (ho : Odd (a j.val)) (hnz : G j≠0)
    (hside : ¬CommonOneSided (kCoordinates (original G))) :
    ∃ D : GeneralOddMinimalTerminal.Minimal G,
      D.arity=supportGcd G ∧ 0<D.arity ∧
      Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Loops.NoCuts D.graph.denote ∧
      Nonempty (GeneralOddHighTerminalAccess.Reduction G (GeneralOddMinimalTerminal.actual G D)) := by
  let D := GeneralOddMinimalTerminal.select G j ho hnz
  exact ⟨D,minimal_arity_eq_supportGcd G D hside,
    by obtain ⟨k,hk⟩ := D.odd; omega,
    GeneralOddMinimalTerminal.noCuts G D,⟨GeneralOddMinimalTerminal.controlled G D⟩⟩

/-- Every nonprimitive residue excludes all actual nonzero original unaries.
The high arm is a harmonic actual graph, not an asserted hardness witness. -/
theorem source_cases (j : Fin s) (ho : Odd (a j.val)) (hnz : G j≠0)
    (hnot : ¬Tract (original G)) :
    (CommonOneSided (kCoordinates (preprocess (original G))) ∧
      ¬EOTract (centralFamily (kCoordinates (preprocess (original G))))) ∨
    (supportGcd G=1 ∧ ∃U : GeneralOddHighTerminalAccess.Actual G 1,
      U.graph.denote≠0 ∧ Nonempty (GeneralOddHighTerminalAccess.Reduction G U)) ∨
    (∃ D : GeneralOddMinimalTerminal.Minimal G,
      3≤D.arity ∧ D.arity=supportGcd G ∧
      sourceKBasis.symm.action D.graph.denote=
        Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Structure.twoConstants
          (sourceKBasis.symm.action D.graph.denote (fun _=>false))
          (sourceKBasis.symm.action D.graph.denote (fun _=>true)) ∧
      Nonempty (GeneralOddHighTerminalAccess.Reduction G (GeneralOddMinimalTerminal.actual G D)) ∧
      ∀U : GeneralOddHighTerminalAccess.Actual G 1,U.graph.denote=0) := by
  by_cases hs : CommonOneSided (kCoordinates (preprocess (original G)))
  · exact .inl ⟨hs,oneSided_eo_failure G hnot hs⟩
  have hside : ¬CommonOneSided (kCoordinates (original G)) := by
    intro h
    exact hs (h.mono_family (Set.image_mono (fun _ h=>h.1)))
  by_cases hp : supportGcd G=1
  · exact .inr (.inl ⟨hp,source_unary G j ho hnz hside hp⟩)
  obtain ⟨D,he,hpos,hcuts,hred⟩ := source_exact G j ho hnz hside
  have hh : 3≤D.arity := by obtain ⟨k,hk⟩ := D.odd; omega
  refine .inr (.inr ⟨D,hh,he,?_,hred,?_⟩)
  · exact Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Structure.ordinary_terminal_decomposition D.graph.denote D.odd hh hcuts
  · intro U
    by_contra hU
    exact hp (unary_forces_primitive G U.graph U.uses U.ordinary hU)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddResidueSource
