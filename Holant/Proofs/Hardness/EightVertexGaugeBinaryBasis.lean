import Holant.Proofs.Hardness.EightVertexGaugeAffine
import Holant.Marked.Groups

/-! The same gauge basis covers the entire displayed monomial binary group
once its phases have fourth power one. This lemma does not assume that these
phase restrictions follow from stability; the physical producer must supply
that proof. The inverse vertex action and native edge action stay distinct. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeBinaryBasis
open Holant Holant.Tractable Holant.Marked
open EightVertexGaugeAffine

private theorem monomial_affine (p : Bool) (r : AlgebraicComplex) (hr : r^4=1) :
    Affine (kernelSignature (if p then S r else R r)) := by
  obtain ⟨q,hq⟩ := fourthRootPhase_surjective_of_pow_four hr
  let A : AffineSystem 2 := ⟨1,fun _ _ => 1,fun _ => if p then 1 else 0⟩
  let Q : QuadraticPhase 2 := ⟨0,![0,q],fun _ _ => 0,fun _ _ _ => Or.inl rfl⟩
  have holds (x : Fin 2→Bool) : A.Holds x ↔ (x 0 != x 1)=p := by
    change (∀ _ : Fin 1, (∑ j : Fin 2, (1 : ZMod 2)*bitValue (ZMod 2) (x j)) =
      (if p then 1 else 0)) ↔ _
    simp only [Fin.forall_fin_one,Fin.sum_univ_two,one_mul]
    cases p <;> cases x 0 <;> cases x 1 <;> decide
  convert affine_formula 1 A Q using 1
  funext x
  cases p <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature,R,S,Kernel.mul_apply,Signature.disequality,diagonalKernel,
      affineFormula,holds,h0,h1,Q,QuadraticPhase.eval,Fin.sum_univ_two,bitValue,hq]

theorem diagonal_vertex_action (t : AlgebraicComplex) (ht : t≠0)
    (c r : AlgebraicComplex) :
    (diagonalBasis t ht).symm.action (kernelSignature (scale c (R r))) =
      fun x => c * kernelSignature (R (r*(t⁻¹)^2)) x := by
  change Signature.coordinateAction (fun _ => diagonalKernel 1 t⁻¹) _ = _
  rw [coordinateAction_diagonal]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature,R,scale,diagonalKernel,diagonalCoefficient,
      Fin.prod_univ_two,h0,h1,pow_two] <;> ring

theorem anti_vertex_action (t : AlgebraicComplex) (ht : t≠0)
    (c r : AlgebraicComplex) :
    (diagonalBasis t ht).symm.action (kernelSignature (scale c (S r))) =
      fun x => (c*t⁻¹) * kernelSignature (S r) x := by
  change Signature.coordinateAction (fun _ => diagonalKernel 1 t⁻¹) _ = _
  rw [coordinateAction_diagonal]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature,R,S,scale,Kernel.mul_apply,Signature.disequality,
      diagonalKernel,diagonalCoefficient,Fin.prod_univ_two,h0,h1] <;> ring

/-- Every binary representative uses exactly the basis already selected for
all gauge rows, including arbitrary nonzero projective scales. -/
theorem group_affine {m : ℕ} (t : AlgebraicComplex) (ht : t≠0) (h8 : t^8=1)
    (phases : ∀ r : AlgebraicComplex, Roots m r → r^4=1)
    (B : Mat) (member : B∈groupM m) :
    Affine ((diagonalBasis t ht).symm.action (kernelSignature B)) := by
  rcases member with ⟨r,hr,⟨c,hc,rfl⟩ | ⟨c,hc,rfl⟩⟩
  · rw [diagonal_vertex_action]
    apply Affine.scale
    have hh : (r*(t⁻¹)^2)^4=1 := by
      rw [mul_pow,phases r hr,one_mul,←pow_mul]
      norm_num only [show 2*4=8 by decide]
      rw [inv_pow,h8,inv_one]
    exact monomial_affine false _ hh
  · rw [anti_vertex_action]
    exact (monomial_affine true r (phases r hr)).scale (c*t⁻¹)

/-- Union with all native monomial binary vertices preserves the SAME basis
and the already proved native edge condition. -/
theorem common_basis_with_binaries {m : ℕ} (F : SignatureFamily AlgebraicComplex)
    (t : AlgebraicComplex) (ht : t≠0) (h8 : t^8=1)
    (phases : ∀ r : AlgebraicComplex, Roots m r → r^4=1)
    (basis : IsCommonKBasis affineClass F (diagonalBasis t ht)) :
    IsCommonKBasis affineClass
      (F ∪ {f | ∃ B : Mat, B∈groupM m ∧ f=⟨2,kernelSignature B⟩})
      (diagonalBasis t ht) := by
  refine ⟨basis.1,?_⟩
  rintro f (hf | ⟨B,hB,rfl⟩)
  · exact basis.2 f hf
  · exact group_affine t ht h8 phases B hB

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeBinaryBasis
end
