import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorAffineBasis
import Holant.Tractable.Conformal.CommonBasis
import Mathlib.Tactic.DeriveFintype

/-! A concrete finite family of inverse matrices for an affine common basis.
The six unary lines, three tensor probes, five affine ratios and fourth roots
are all explicitly indexed. Scalar normalization preserves both all rows and
the actual ordinary edge, giving an exact finite common-basis criterion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorAffineBasisCandidates
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open StableHigherCurrentAnchorAffineBasis
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option Elab.async false

structure Code where
  first : LineCode
  second : LineCode
  reference : Fin 3
  sample : Fin 3
  ratio : PhaseCode
  deriving DecidableEq,Fintype

def fourthPower (i : Code) : AlgebraicComplex :=
  (phase i.ratio*fourthTensor (line i.first) (probe i.reference)-
    fourthTensor (line i.first) (probe i.sample))/
  (fourthTensor (line i.second) (probe i.sample)-
    phase i.ratio*fourthTensor (line i.second) (probe i.reference))

/-- First column normalized to one of six lines; second column retains the
single relative scale. Zero denominators may add candidates, never lose one. -/
def inverseCandidate (i : Code) (t : AlgebraicComplex) : Kernel AlgebraicComplex :=
  fun a b=>if b then t*line i.second a else line i.first a

def inverseCandidates : Finset (Kernel AlgebraicComplex) := by
  classical
  exact Finset.univ.biUnion fun i : Code=>
    (Polynomial.nthRootsFinset 4 (fourthPower i)).image (inverseCandidate i)

/-- Uniform, family-independent size bound; duplicate candidates only reduce it. -/
theorem inverseCandidates_card_le : inverseCandidates.card ≤ 6480 := by
  classical
  have hc : Fintype.card Code=1620 := by decide
  calc
    inverseCandidates.card ≤ ∑i : Code,
        ((Polynomial.nthRootsFinset 4 (fourthPower i)).image (inverseCandidate i)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑_i : Code,4 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.card_image_le.trans
      rw [Polynomial.nthRootsFinset_def]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 4 (fourthPower i))
    _ = 6480 := by simp [hc]

/-- The original inverse matrix is exactly a nonzero scalar times one member
of the fixed finite list. The list is independent of the input family. -/
theorem common_basis_candidates {H : SignatureFamily AlgebraicComplex} (B : InvertibleKernel)
    (h0 : (⟨1,pin false⟩ : AnySignature AlgebraicComplex)∈H)
    (h1 : (⟨1,pin true⟩ : AnySignature AlgebraicComplex)∈H)
    (heq : (⟨4,eq4⟩ : AnySignature AlgebraicComplex)∈H)
    (hB : IsCommonBasis affineClass H B) :
    ∃c : AlgebraicComplex,c≠0 ∧ ∃N∈inverseCandidates,
      B.inverse=fun a b=>c*N a b := by
  classical
  obtain ⟨c,d,hc,hd,p,q,hp,hq⟩ := inverse_columns B h0 h1 hB
  have hi : line p false*line q true-line q false*line p true≠0 := by
    intro hi
    have hz : determinant B.inverse=c*d*(line p false*line q true-line q false*line p true) := by
      simp only [determinant,hp,hq]
      ring
    have hn := determinant_ne_zero B.symm
    exact hn (by change determinant B.inverse=0; rw [hz,hi,mul_zero])
  have he : B.symm.action eq4=fun x=>c^4*fourthTensor (line p) x+d^4*fourthTensor (line q) x := by
    funext x
    change Signature.coordinateAction (fun _=>B.inverse) eq4 x=_
    rw [StableHigherCurrentAnchorCriterion.action_eq4]
    simp only [hp,hq,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rfl
  have hf : Affine (fun x=>c^4*fourthTensor (line p) x+d^4*fourthTensor (line q) x) := by
    rw [←he]
    exact hB.2 _ heq
  obtain ⟨x,y,r,_,hr⟩ := relative_scale_constraint (line p) (line q) c d hc hi hf
  let i : Code := ⟨p,q,x,y,r⟩
  refine ⟨c,hc,inverseCandidate i (d/c),?_,?_⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨d/c,?_,rfl⟩⟩
    apply (Polynomial.mem_nthRootsFinset (by decide : 0<4) (fourthPower i)).mpr
    exact hr
  · funext a b
    cases b
    · simpa [inverseCandidate,i] using hp a
    · simp only [inverseCandidate,ite_true,i]
      rw [hq]
      field_simp

/-- Uniform scalar multiplication of an actual invertible basis. -/
def rescale (B : InvertibleKernel) (c : AlgebraicComplex) (hc : c≠0) : InvertibleKernel where
  matrix := fun a b=>c*B.matrix a b
  inverse := fun a b=>c⁻¹*B.inverse a b
  matrix_inverse := by
    funext a b
    have h := congrFun (congrFun B.matrix_inverse a) b
    simp only [Kernel.mul_apply] at h ⊢
    calc
      _=B.matrix a false*B.inverse false b+B.matrix a true*B.inverse true b := by field_simp
      _=_ := h
  inverse_matrix := by
    funext a b
    have h := congrFun (congrFun B.inverse_matrix a) b
    simp only [Kernel.mul_apply] at h ⊢
    calc
      _=B.inverse a false*B.matrix false b+B.inverse a true*B.matrix true b := by field_simp
      _=_ := h

theorem action_scale (M : Kernel AlgebraicComplex) (c : AlgebraicComplex)
    {n : ℕ} (f : Signature AlgebraicComplex n) :
    Signature.coordinateAction (fun _ a b=>c*M a b) f=
      fun x=>c^n*Signature.coordinateAction (fun _=>M) f x := by
  funext x
  simp only [Signature.coordinateAction,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The edge acquires its genuine square scale; each arity-n row acquires
its genuine inverse n-th scale. Affine membership retains both certificates. -/
theorem rescale_common {H : SignatureFamily AlgebraicComplex} (B : InvertibleKernel)
    (c : AlgebraicComplex) (hc : c≠0) (hB : IsCommonBasis affineClass H B) :
    IsCommonBasis affineClass H (rescale B c hc) := by
  constructor
  · have he : Kernel.pullback Signature.equality (rescale B c hc).matrix=
        fun a b=>c^2*Kernel.pullback Signature.equality B.matrix a b := by
      funext a b
      simp only [rescale,Kernel.pullback,Kernel.mul_apply,Kernel.transpose]
      ring
    change Affine (kernelSignature (Kernel.pullback Signature.equality (rescale B c hc).matrix))
    rw [he]
    exact Affine.scale hB.1 (c^2)
  · intro f hf
    change Affine (Signature.coordinateAction (fun _ a b=>c⁻¹*B.inverse a b) f.2)
    rw [action_scale]
    exact Affine.scale (hB.2 f hf) (c⁻¹^f.1)

/-- Two genuine invertible kernels with the same inverse have the same matrix. -/
theorem basis_eq_of_inverse (B D : InvertibleKernel) (he : B.inverse=D.inverse) : B=D := by
  have hm : B.matrix=D.matrix := by
    calc
      B.matrix=Kernel.mul B.matrix Signature.equality := (Kernel.mul_equality _).symm
      _=Kernel.mul B.matrix (Kernel.mul D.inverse D.matrix) := by rw [D.inverse_matrix]
      _=Kernel.mul (Kernel.mul B.matrix B.inverse) D.matrix := by rw [he,Kernel.mul_assoc]
      _=D.matrix := by rw [B.matrix_inverse,Kernel.equality_mul]
  cases B
  cases D
  cases hm
  cases he
  rfl

/-- All rows and the mandatory edge have one normalized basis from the fixed
finite candidate set. No per-signature choice or additional hypothesis occurs. -/
theorem common_transformable_iff_candidates {H : SignatureFamily AlgebraicComplex}
    (h0 : (⟨1,pin false⟩ : AnySignature AlgebraicComplex)∈H)
    (h1 : (⟨1,pin true⟩ : AnySignature AlgebraicComplex)∈H)
    (heq : (⟨4,eq4⟩ : AnySignature AlgebraicComplex)∈H) :
    CommonTransformable affineClass H ↔ H.Finite ∧
      ∃N∈inverseCandidates,∃hN : determinant N≠0,
        IsCommonBasis affineClass H (invertibleOfDeterminant N hN).symm := by
  constructor
  · rintro ⟨hfin,B,hB⟩
    obtain ⟨c,hc,N,hN,he⟩ := common_basis_candidates B h0 h1 heq hB
    let D := rescale B c hc
    have hi : D.inverse=N := by
      funext a b
      change c⁻¹*B.inverse a b=N a b
      rw [he]
      simp [hc]
    have hn : determinant N≠0 := by
      rw [←hi]
      exact determinant_ne_zero D.symm
    have hd : D=(invertibleOfDeterminant N hn).symm :=
      basis_eq_of_inverse _ _ hi
    refine ⟨hfin,N,hN,hn,?_⟩
    rw [←hd]
    exact rescale_common B c hc hB
  · rintro ⟨hfin,N,_,hN,hB⟩
    exact ⟨hfin,(invertibleOfDeterminant N hN).symm,hB⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorAffineBasisCandidates
end
