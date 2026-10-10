import Holant.Proofs.Hardness.EOBinaryPlaneCore
import Holant.Proofs.Reductions.EightVertexNonexception.SparseExclusions
import Holant.Proofs.Tractability.EOEvaluation.PairLift

/-! Actual affine/product witnesses for opposite-pair EO planes. Signed
coordinate substitutions preserve the literal product factors; no class oracle
or tractability conclusion is assumed in the binary compression. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneTract
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace C
export EOBinaryPlaneCore (pairing word compress lift pairing_word restrict_eq compress_lift lift_eo
  normalized normalized_eo normalized_lift)
end C
namespace L
export Holant.LocalDrafts.Tractability.EOEvaluation.PairLift
  (Compatible restrict indicator affine_lift product_lift product_coordinates)
end L
set_option backward.isDefEq.respectTransparency false

/-- Negating a selected variable only interchanges equality and disequality. -/
theorem signed_equality {n : ℕ} (i j : Fin n) (a b : Bool) :
    Product (fun x : Fin n→Bool => Signature.equality (K:=AlgebraicComplex)
      (if a then !(x i) else x i) (if b then !(x j) else x j)) := by
  cases a <;> cases b
  · exact product_equality i j
  · convert product_disequality i j using 1
    funext x
    cases x i <;> cases x j <;> rfl
  · convert product_disequality i j using 1
    funext x
    cases x i <;> cases x j <;> rfl
  · convert product_equality i j using 1
    funext x
    cases x i <;> cases x j <;> rfl

theorem signed_disequality {n : ℕ} (i j : Fin n) (a b : Bool) :
    Product (fun x : Fin n→Bool => Signature.disequality (K:=AlgebraicComplex)
      (if a then !(x i) else x i) (if b then !(x j) else x j)) := by
  cases a <;> cases b
  · exact product_disequality i j
  · convert product_equality i j using 1
    funext x
    cases x i <;> cases x j <;> rfl
  · convert product_equality i j using 1
    funext x
    cases x i <;> cases x j <;> rfl
  · convert product_disequality i j using 1
    funext x
    cases x i <;> cases x j <;> rfl

def signedMap {m n : ℕ} (ports : Fin n→Fin m×Bool) (x : Fin m→Bool) : Fin n→Bool :=
  fun j=>if (ports j).2 then !(x (ports j).1) else x (ports j).1

theorem signed_factor {m n : ℕ} (ports : Fin n→Fin m×Bool) (p : ProductFactor n) :
    Product (fun x=>p.eval (signedMap ports x)) := by
  cases p with
  | unary j u hu => exact product_unary (ports j).1 (fun b=>u (if (ports j).2 then !b else b))
  | equality i j => exact signed_equality (ports i).1 (ports j).1 (ports i).2 (ports j).2
  | disequality i j => exact signed_disequality (ports i).1 (ports j).1 (ports i).2 (ports j).2

theorem signed_list {m n : ℕ} (ports : Fin n→Fin m×Bool) (ps : List (ProductFactor n)) :
    Product (fun x=>(ps.map fun p=>p.eval (signedMap ports x)).prod) := by
  induction ps with
  | nil => exact product_constant m 1
  | cons p ps ih => exact (signed_factor ports p).mul ih

theorem product_signed {m n : ℕ} (ports : Fin n→Fin m×Bool)
    {f : Signature AlgebraicComplex n} (hf : Product f) : Product (fun x=>f (signedMap ports x)) := by
  rcases hf with rfl|⟨s,hs,ps,rfl⟩
  · exact product_zero m
  · exact (signed_list ports ps).scale s

theorem pairing_affine {n : ℕ} (p : OrientedPerfectPairing n) : TwoTranslate.IsAffineMap p.word := by
  intro x y
  funext j
  simp only [OrientedPerfectPairing.word,AffinePhase.xor,AffinePhase.origin]
  cases (p.ports.symm j).2 <;> cases x (p.ports.symm j).1 <;> cases y (p.ports.symm j).1 <;> rfl

theorem eoTract_of_affine (M : Signature AlgebraicComplex 4) (he : DenseEOUnitLocal.EOSupport M)
    (hf : Affine M) : EOTract {⟨4,M⟩} := by
  refine ⟨by simp,?_,.positive,.affine,?_,?_⟩
  · intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    refine ⟨⟨2,rfl⟩,?_⟩
    intro x hx
    change 2*Holant.weight x≠4 at hx
    exact he x (by omega)
  · intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    intro a b c ha hb hc
    exact Or.inl (affine_support_xor3 hf a b c ha hb hc)
  · intro g hg p
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact hf.precompose p.word (pairing_affine p)

theorem eoTract_of_product (M : Signature AlgebraicComplex 4) (he : DenseEOUnitLocal.EOSupport M)
    (hf : Product M) : EOTract {⟨4,M⟩} := by
  refine ⟨by simp,?_,.positive,.product,?_,?_⟩
  · intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    refine ⟨⟨2,rfl⟩,?_⟩
    intro x hx
    change 2*Holant.weight x≠4 at hx
    exact he x (by omega)
  · intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    intro a b c ha hb hc
    exact Or.inl (product_support_xor3 hf a b c ha hb hc)
  · intro g hg p
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact product_signed p.ports.symm hf

private theorem pairing_compatible (x : Fin 4→Bool) :
    L.Compatible C.pairing x ↔ x 1=!(x 0) ∧ x 3=!(x 2) := by
  change (∀j : Fin 2,x (C.pairing.ports (j,false))≠x (C.pairing.ports (j,true))) ↔ _
  simp only [Fin.forall_fin_two]
  change (x 0≠x 1 ∧ x 2≠x 3) ↔ x 1=!(x 0) ∧ x 3=!(x 2)
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

theorem restrict_lift (f : Signature AlgebraicComplex 2) : L.restrict C.pairing (C.lift f)=C.lift f := by
  funext x
  by_cases h : x 1=!(x 0) ∧ x 3=!(x 2)
  · simp [L.restrict,pairing_compatible,h]
  · simp [L.restrict,pairing_compatible,C.lift,h]

theorem affine_lift {f : Signature AlgebraicComplex 2} (hf : Affine f) : Affine (C.lift f) := by
  rw [←restrict_lift]
  apply L.affine_lift
  simpa only [C.restrict_eq,C.compress_lift] using hf

theorem product_lift {f : Signature AlgebraicComplex 2} (hf : Product f) : Product (C.lift f) := by
  rw [←restrict_lift]
  apply L.product_lift
  simpa only [C.restrict_eq,C.compress_lift] using hf

/-- Exact source criterion for the literal binary-plane lift. -/
theorem lift_tract_iff (f : Signature AlgebraicComplex 2) :
    EOTract {⟨4,C.lift f⟩} ↔ Affine f ∨ Product f := by
  constructor
  · rintro ⟨_,_,sign,cl,hs,hc⟩
    have h := hc ⟨4,C.lift f⟩ (by simp) C.pairing
    rw [C.restrict_eq,C.compress_lift] at h
    cases cl
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h|h)
    · exact eoTract_of_affine (C.lift f) (C.lift_eo f) (affine_lift h)
    · exact eoTract_of_product (C.lift f) (C.lift_eo f) (product_lift h)

/-- Pairings transform contravariantly under the original ordered port map. -/
def transportPairing {n : ℕ} (e : Equiv.Perm (Fin n)) (p : OrientedPerfectPairing n) :
    OrientedPerfectPairing n := ⟨p.count,p.ports.trans e.symm⟩

theorem restriction_reindex {n : ℕ} (e : Equiv.Perm (Fin n)) (p : OrientedPerfectPairing n)
    (M : Signature AlgebraicComplex n) :
    (transportPairing e p).restrict M=p.restrict (Tensor.reindex e M) := rfl

theorem affine_unreindex {n : ℕ} (e : Equiv.Perm (Fin n)) (M : Signature AlgebraicComplex n)
    (h : Affine (Tensor.reindex e M)) : Affine M := by
  have hh := h.precompose (fun x j=>x (e.symm j)) (coordinates_isAffineMap e.symm)
  change Affine (Tensor.reindex e.symm (Tensor.reindex e M)) at hh
  simpa only [Tensor.reindex_symm] using hh

theorem product_unreindex {n : ℕ} (e : Equiv.Perm (Fin n)) (M : Signature AlgebraicComplex n)
    (h : Product (Tensor.reindex e M)) : Product M := by
  have hh := L.product_coordinates e.symm h
  change Product (Tensor.reindex e.symm (Tensor.reindex e M)) at hh
  simpa only [Tensor.reindex_symm] using hh

/-- Every one of the three affine planes uses the same actual compressed
binary criterion, retaining all coefficient values and the original ports. -/
theorem plane_tract_iff (M : Signature AlgebraicComplex 4) (he : DenseEOUnitLocal.EOSupport M)
    (i : Fin 6) (h0 : FiveSupportEOOrdering.middleCoeff M i=0)
    (h1 : FiveSupportEOOrdering.middleCoeff M (5-i)=0) :
    EOTract {⟨4,M⟩} ↔ Affine (C.compress (C.normalized M i)) ∨ Product (C.compress (C.normalized M i)) := by
  constructor
  · rintro ⟨_,_,sign,cl,hs,hc⟩
    have h := hc ⟨4,M⟩ (by simp)
      (transportPairing (FiveSupportEOOrdering.orderAt i) C.pairing)
    rw [restriction_reindex,C.restrict_eq] at h
    cases cl
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h|h)
    · have hh := affine_lift h
      rw [C.normalized_lift M he i h0 h1] at hh
      exact eoTract_of_affine M he (affine_unreindex (FiveSupportEOOrdering.orderAt i) M hh)
    · have hh := product_lift h
      rw [C.normalized_lift M he i h0 h1] at hh
      exact eoTract_of_product M he (product_unreindex (FiveSupportEOOrdering.orderAt i) M hh)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneTract
