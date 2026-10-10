import Holant.Proofs.Closure.ClosureStableFactorLines
import Holant.Proofs.Closure.ClosureStableFactorPorts
import Holant.Proofs.Closure.ClosureCompatibleAlignmentFusion

/-! Shared pure reconstruction for an internally constructed family of actual
nonzero M cards. B/A transports may supply their proved source families here;
the final source factories do not accept this record as an extra oracle. All
zero samples remain in the same exact tensor-factor linear subspace. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureBStableFactor
open Holant Holant.Tractable Holant.Marked
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine
open Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureStableFactor

def Sample (m r : ℕ) (f : Signature Scalar (2*r+4)) :=
  {i : Bool × {t : Scalar // Roots m t} // Signature.contract (M i.1 i.2.val) f≠0}

theorem sample_nonempty {m r : ℕ} (hm : 3≤m) (f : Signature Scalar (2*r+4)) (nonzero : f≠0) :
    Nonempty (Sample m r f) := by
  classical
  by_contra none
  have zero (p : Bool) (t : {t : Scalar // Roots m t}) : Signature.contract (M p t.val) f=0 := by
    by_contra live
    exact none ⟨⟨(p,t),live⟩⟩
  let t₀ : {t : Scalar // Roots m t} := ⟨1,Roots.one m⟩
  obtain ⟨t₁,square⟩ := ClosureCompatibleAlignment.root_square_avoids hm 1
  have different : t₀.val≠t₁.val := by
    intro h
    apply square
    simp only [←h,t₀,one_pow]
  have card (i : Bool × Bool) (a b : Bool) (x : Fin (2*r) → Bool) :
      close i.1 (phase t₀.val t₁.val i) f (pair a b x)=Signature.equality a b*(0 : Scalar) := by
    cases i with
    | mk p bit =>
      cases bit
      · simpa only [phase,reduceCtorEq,ite_false,Pi.zero_apply,mul_zero,close,Signature.contract] using congrFun (zero p t₀) (pair a b x)
      · simpa only [phase,ite_true,Pi.zero_apply,mul_zero,close,Signature.contract] using congrFun (zero p t₁) (pair a b x)
  have inversion := four_card_inversion t₀.val t₁.val different f Signature.equality
    (fun _ => (0 : Signature Scalar (2*r))) card
  apply nonzero
  funext w
  have reconstruct : pair (w 0) (w 1) (pair (tail w 0) (tail w 1) (tail (tail w)))=w := by
    rw [pair_eta,pair_eta]
  have h := inversion (w 0) (w 1) (tail w 0) (tail w 1) (tail (tail w))
  rw [reconstruct] at h
  simpa [inverseSlices] using h

def canonicalAnchor {m r : ℕ} (hm : 3≤m) (f : Signature Scalar (2*r+4)) (nonzero : f≠0) : Sample m r f :=
  Classical.choice (sample_nonempty hm f nonzero)

structure Family (m r : ℕ) (f : Signature Scalar (2*r+4)) where
  anchor : Sample m r f
  ports : (Fin (r+1) × Bool) ≃ Fin (2*r+2)
  tables : Sample m r f → Fin (r+1) → Mat
  coefficient : Sample m r f → Scalar
  equation : ∀ i,Signature.contract (M i.val.1 i.val.2.val) f=
    productValue ports (tables i) (coefficient i)
  distance : ∀ i j e d,e≠d → ProjectivelyEqual (tables j e) (tables i e) ∨
    ProjectivelyEqual (tables j d) (tables i d)

namespace Family
variable {m r : ℕ} {f : Signature Scalar (2*r+4)} (F : Family m r f)

theorem fixed_edge (large : 2≤r) : ∃ e : Fin (r+1),∀ i,ProjectivelyEqual (F.tables i e) (F.tables F.anchor e) := by
  let : NeZero r := ⟨by omega⟩
  exact projective_fixed_coordinate F.tables F.anchor F.distance

def residualOrder (e : Fin (r+1)) : Equiv.Perm (Fin (2*r+2)) := ClosureStableFactor.pairOrder (F.ports (e,false)) (F.ports (e,true))

theorem residual_first (e : Fin (r+1)) : F.residualOrder e 0=F.ports (e,false) := by
  apply ClosureStableFactor.pairOrder_first
  intro h
  have eq := congrArg Prod.snd (F.ports.injective h)
  cases eq

theorem residual_second (e : Fin (r+1)) : F.residualOrder e 1=F.ports (e,true) := ClosureStableFactor.pairOrder_second _ _

def ancestor (e : Fin (r+1)) : Signature Scalar (2*r+4) := Tensor.reindex (liftResidual (F.residualOrder e)).symm f

theorem every_sample (e : Fin (r+1)) (fixed : ∀ i,ProjectivelyEqual (F.tables i e) (F.tables F.anchor e))
    (p : Bool) (t : {t : Scalar // Roots m t}) :
    ∃ R : Signature Scalar (2*r),∀ b c x,close p t.val (F.ancestor e) (pair b c x)=F.tables F.anchor e b c*R x := by
  classical
  let u := F.residualOrder e
  have transport : close p t.val (F.ancestor e)=Tensor.reindex u.symm (Signature.contract (M p t.val) f) :=
    close_liftResidual u f p t.val
  by_cases zero : Signature.contract (M p t.val) f=0
  · refine ⟨0,?_⟩
    intro b c x
    rw [congrFun transport (pair b c x),zero]
    simp [Tensor.reindex]
  · let i : Sample m r f := ⟨(p,t),zero⟩
    let ports := F.ports.trans u.symm
    have first : ports (e,false)=0 := by
      change u.symm (F.ports (e,false))=0
      rw [←F.residual_first e]
      exact u.symm_apply_apply 0
    have second : ports (e,true)=1 := by
      change u.symm (F.ports (e,true))=1
      rw [←F.residual_second e]
      exact u.symm_apply_apply 1
    obtain ⟨R,eq⟩ := product_fixed_factor ports (F.tables i) (F.coefficient i) e first second _ (fixed i)
    refine ⟨R,?_⟩
    intro b c x
    rw [congrFun transport (pair b c x)]
    change Signature.contract (M i.val.1 i.val.2.val) f (fun j => pair b c x (u.symm j))=_
    rw [F.equation i]
    exact eq b c x

/-- The exact binary is the anchor's actual table at the internally selected
fixed edge. Only the genuine phase difference is inverted; sampled zeros are
never divided by, and no common nonzero phase grid is required. -/
theorem split (hm : 3≤m) (large : 2≤r) :
    ∃ e : Fin (r+1),∃ R : Signature Scalar (2*r+2),
      ∃ s : ProperSplit (⟨2*r+4,f⟩ : AnySignature Scalar) ⟨2,kernelSignature (F.tables F.anchor e)⟩ ⟨2*r+2,R⟩,
      s.ports=(factorPorts (2*r)).trans (liftResidual (F.residualOrder e)) ∧ s.scale=1 := by
  classical
  obtain ⟨e,fixed⟩ := F.fixed_edge large
  let u := F.residualOrder e
  let t₀ : {t : Scalar // Roots m t} := ⟨1,Roots.one m⟩
  obtain ⟨t₁,square⟩ := ClosureCompatibleAlignment.root_square_avoids hm 1
  have different : t₀.val≠t₁.val := by
    intro h
    apply square
    simp only [←h,t₀,one_pow]
  have factors (i : Bool × Bool) : ∃ R : Signature Scalar (2*r),∀ b c x,
      close i.1 (phase t₀.val t₁.val i) (F.ancestor e) (pair b c x)=F.tables F.anchor e b c*R x := by
    cases i with
    | mk p bit =>
      cases bit
      · simpa only [phase,reduceCtorEq,ite_false] using F.every_sample e fixed p t₀
      · simpa only [phase,ite_true] using F.every_sample e fixed p t₁
  choose H equations using factors
  let R := inverseSlices t₀.val t₁.val H
  have normalized : F.ancestor e=Tensor.reindex (factorPorts (2*r))
      (Tensor.tensor (kernelSignature (F.tables F.anchor e)) R) :=
    tensor_factor_of_slices _ _ _ (four_card_inversion t₀.val t₁.val different _ _ H equations)
  have original : Tensor.reindex (liftResidual u) (F.ancestor e)=f := by
    funext x
    simp only [ancestor,Tensor.reindex]
    congr 1
    funext j
    simp only [u,Equiv.apply_symm_apply]
  have exactFactor : f=Tensor.reindex ((factorPorts (2*r)).trans (liftResidual u))
      (Tensor.tensor (kernelSignature (F.tables F.anchor e)) R) := by
    calc
      f = Tensor.reindex (liftResidual u) (F.ancestor e) := original.symm
      _ = Tensor.reindex (liftResidual u) (Tensor.reindex (factorPorts (2*r))
        (Tensor.tensor (kernelSignature (F.tables F.anchor e)) R)) := congrArg (Tensor.reindex (liftResidual u)) normalized
      _ = _ := rfl
  exact ⟨e,R,ClosureTensorPrimeFactors.splitOfTensor _ _ _ _ (by omega) (by omega) exactFactor,rfl,rfl⟩

end Family
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureBStableFactor
