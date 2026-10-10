import Holant.Platonic.StabilizerErasure.FullSource
import Holant.Platonic.StabilizerErasure.HilbertAdjoint
import Holant.Platonic.StabilizerErasure.SemanticEncoderFactorization
import Holant.Platonic.StabilizerErasure.SemanticPrecomposition
import Holant.Platonic.StabilizerErasure.EigenvalueCode

/-!
Lemma 9.20 with the source-primary input definition, closing the input
directionality limitation of the earlier concrete-encoder checkpoint.

The input is any actual linear map U with `IsStabilizerIsometry U`: its
image is an exact common eigenspace of commuting actual Paulis, it is an
actual Hilbert isometry, and all logical Paulis have physical representatives.
No Clifford encoder, decoder, frame, rank, or phase witness is assumed.
`hasStabilizerImage_iff_eigenvalues` proves that the common +1 description
also covers the source's arbitrary fourth-root eigenvalue character by
absorbing those exact phases into the actual Pauli generators.

The proof constructs an image-normalizing Clifford, derives the binary code
dimension from Hilbert isometry, constructs a same-range encoder V, and
proves U=VL for an actual logical Clifford L. Exact finite Pauli faithfulness
and finiteness establish both normalizer directions. KL, pure residuals,
mixed residuals (including the auxiliary input), and column coordinates
are then transported through this proved factorization.

`hilbertAdjoint` is the actual Hermitian adjoint of arbitrary U, with its
defining identity proved. `CorrectableMap` is exactly the source's scalar
V†R_rV condition for every one-qubit operator. Nullary output is included.
-/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

def NoCorrectableMap : {k n : ℕ} → (Signature ℂ k →ₗ[ℂ] Signature ℂ n) → Prop
  | _,0,_ => True
  | _,n+1,U => ∀r : Fin (n+1),¬CorrectableMap U r

def ColumnNormalFormMap (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) : Prop :=
  ∃p : Fin n → Fin 4,∃B : AnalyticClifford k,
    ∃c : BinaryVector n,∃M : Matrix (Fin k) (Fin n) (ZMod 2),
      ∃a₀ : ℂ,∃Q : QuadraticPhase k,
        a₀≠0 ∧ M.rank=k ∧ (∀r,M.col r≠0) ∧
        ∀z,Signature.coordinateAction (fun r => axisMatrix (p r))
          (U (B.operator.symm (ket (wordVector z))))=
            (a₀*(fourthRootPhase (Q.eval (wordVector z)) : ℂ)) •
              ket (wordVector (c+M.transpose.mulVec z))

def ErasureAlternativesMap : {k n : ℕ} → (Signature ℂ k →ₗ[ℂ] Signature ℂ n) → Prop
  | _,0,_ => True
  | _,n+1,U => ∀r : Fin (n+1),CorrectableMap U r →
      ∃C : AnalyticClifford (n+1),∃R : Kernel ℂ,
        (∀f,C.operator f=siteAction r R f) ∧
        (PureStabilizerForm (C.operator.toLinearMap.comp U) r ∨
          MixedStabilizerForm (C.operator.toLinearMap.comp U) r) ∧
        ¬(PureStabilizerForm (C.operator.toLinearMap.comp U) r ∧
          MixedStabilizerForm (C.operator.toLinearMap.comp U) r)

theorem source_semantic_correctable_forms
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ (n+1)) (hU : IsStabilizerIsometry U)
    (r : Fin (n+1)) (h : CorrectableMap U r) :
    ∃C : AnalyticClifford (n+1),∃R : Kernel ℂ,
      (∀f,C.operator f=siteAction r R f) ∧
      (PureStabilizerForm (C.operator.toLinearMap.comp U) r ∨
        MixedStabilizerForm (C.operator.toLinearMap.comp U) r) ∧
      ¬(PureStabilizerForm (C.operator.toLinearMap.comp U) r ∧
        MixedStabilizerForm (C.operator.toLinearMap.comp U) r) := by
  obtain ⟨V,L,hfactor⟩ := semantic_encoder_clifford_factorization U hU
  have hc : Correctable V r := by
    rw [hfactor,correctableMap_precompose,correctableMap_encoder] at h
    exact h
  obtain ⟨C,R,hR,he,hx⟩ := source_correctable_erasure_normal_forms V r hc
  refine ⟨C,R,hR,?_,pure_mixed_exclusive _ r⟩
  have hcomp : C.operator.toLinearMap.comp U=
      (C.operator.toLinearMap.comp V.map).comp L.operator.toLinearMap := by
    rw [hfactor]
    rfl
  rw [hcomp]
  exact he.elim (fun hp => Or.inl (pureForm_precompose _ r L hp))
    (fun hm => Or.inr (mixedForm_precompose _ r L hm))

theorem columnNormalForm_logical_factor
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (V : StabilizerIsometry k n)
    (L : AnalyticClifford k) (hfactor : U=V.map.comp L.operator.toLinearMap)
    (h : ColumnNormalForm V) : ColumnNormalFormMap U := by
  obtain ⟨p,B,c,M,a₀,Q,ha,hr,hm,he⟩ := h
  refine ⟨p,composeClifford B L,c,M,a₀,Q,ha,hr,hm,?_⟩
  intro z
  change Signature.coordinateAction (fun r => axisMatrix (p r))
    (U (L.operator.symm (B.operator.symm (ket (wordVector z)))))=_
  rw [hfactor]
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  exact he z

theorem source_semantic_column_normal_form
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (hU : IsStabilizerIsometry U)
    (h : NoCorrectableMap U) : ColumnNormalFormMap U := by
  obtain ⟨V,L,hfactor⟩ := semantic_encoder_clifford_factorization U hU
  have hn : NoCorrectableErasure V := by
    cases n with
    | zero => trivial
    | succ n =>
      intro r hr
      apply h r
      rw [hfactor,correctableMap_precompose,correctableMap_encoder]
      exact hr
  exact columnNormalForm_logical_factor U V L hfactor (source_column_normal_form_tensor V hn)

/-- Full Lemma 9.20 for an arbitrary source-primary stabilizer isometry.
In particular no encoder/decoder or alignment witness is an extra premise. -/
theorem source_semantic_stabilizer_erasure_column_normal_form
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) (hU : IsStabilizerIsometry U) :
    ErasureAlternativesMap U ∧ (NoCorrectableMap U → ColumnNormalFormMap U) := by
  constructor
  · cases n with
    | zero => trivial
    | succ n => exact fun r h => source_semantic_correctable_forms U hU r h
  · exact source_semantic_column_normal_form U hU

/-- The same full conclusion directly from a commuting Pauli eigenspace
with arbitrary actual fourth-root eigenvalues, as in the source wording. -/
theorem source_eigenvalue_stabilizer_erasure_column_normal_form
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (hiso : ∀f g,hermitian (U f) (U g)=hermitian f g)
    (himage : HasPauliEigenspaceImage U)
    (hlogical : ∀Q : Pauli k,∃P : Pauli n,∀f,P.run (U f)=U (Q.run f)) :
    ErasureAlternativesMap U ∧ (NoCorrectableMap U → ColumnNormalFormMap U) :=
  source_semantic_stabilizer_erasure_column_normal_form U
    ⟨hiso,(hasStabilizerImage_iff_eigenvalues U).mpr himage,hlogical⟩

end
end Holant.Platonic.StabilizerErasure
