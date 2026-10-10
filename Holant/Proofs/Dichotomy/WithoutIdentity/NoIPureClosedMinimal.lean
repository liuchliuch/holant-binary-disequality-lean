import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMinimalRank
import Holant.Proofs.Hardness.GeneralEONegativeSupportClosure

/-! Genuine original-port minimum-rank descent from ternary-closed support.
No condition on the square of the coefficient row is needed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureClosedMinimal
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
open OrdinaryNegativeSparseMinimalRank
namespace C
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport (Closed)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
variable {n m r : ℕ}

theorem affine_triple (p : Word m→Word n) (hp : IsAffineMap p) (x y z : Word m) :
    p (tripleXor x y z)=tripleXor (p x) (p y) (p z) := by
  change p (xor (xor x y) z)=xor (xor (p x) (p y)) (p z)
  rw [hp,hp]
  funext i
  simp only [AffinePhase.xor]
  generalize p x i=a
  generalize p y i=b
  generalize p z i=c
  generalize p (origin m) i=d
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem closed_precompose {f : Signature AlgebraicComplex n} (closed : C.Closed f)
    (p : Word m→Word n) (hp : IsAffineMap p) : C.Closed (fun x=>f (p x)) := by
  intro x y z hx hy hz
  change f (p (tripleXor x y z))≠0
  rw [affine_triple p hp]
  exact closed _ _ _ hx hy hz

theorem support_system (f : Signature AlgebraicComplex n) (closed : C.Closed f)
    (nonzero : f≠0) : ∃S : AffineSystem n,∀x,S.Holds x↔f x≠0 := by
  obtain ⟨a,ha⟩:=OrdinaryNegativeAffineSquareSupport.exists_base f nonzero
  obtain ⟨S,p,hp,hn,hfix,hS⟩:=
    Holant.ReedMuller.AffinePatching.exists_support_retraction f a ha closed
  exact ⟨S,hS⟩

theorem systematic (f : Signature AlgebraicComplex n) (closed : C.Closed f)
    (nonzero : f≠0) : ∃r : ℕ,Nonempty (SystematicSupport f r) := by
  obtain ⟨a,ha⟩:=OrdinaryNegativeAffineSquareSupport.exists_base f nonzero
  exact exists_systematic f a ha closed

/-- The physical support chart itself certifies ternary closure. -/
theorem chart_closed {f : Signature AlgebraicComplex n} (D : SystematicSupport f r) :
    C.Closed f := by
  intro x y z hx hy hz
  let px : Word r:=fun i=>x (D.ports i)
  let py : Word r:=fun i=>y (D.ports i)
  let pz : Word r:=fun i=>z (D.ports i)
  have h:=D.supported (tripleXor px py pz)
  rw [affine_triple D.encode D.affine,D.covers x hx,D.covers y hy,D.covers z hz] at h
  exact h

theorem chart_nonzero {f : Signature AlgebraicComplex n} (D : SystematicSupport f r) :
    f≠0 := fun h=>D.supported (origin r) (congrFun h _)

theorem nonAffine_reduced {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)
    (bad : ¬Affine f) : ¬Affine D.reduced := by
  obtain ⟨S,hS⟩:=support_system f (chart_closed D) (chart_nonzero D)
  exact fun ha=>bad (D.affine_of_reduced S hS ha)

theorem rank_positive {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)
    (bad : ¬Affine f) : 1≤r := by
  by_contra hr
  have hr0:r=0:=by omega
  subst r
  apply nonAffine_reduced D bad
  convert affine_constant 0 (D.reduced (origin 0)) using 1
  funext x
  congr 1
  funext i
  exact Fin.elim0 i

/-- The physical arity retains every dependent original column. Only actual
information ports outside a face are pinned. -/
theorem exists_low_rank (f : Signature AlgebraicComplex n) (closed : C.Closed f)
    (nonzero : f≠0) (bad : ¬Affine f) :
    ∃r : ℕ,∃D : SystematicSupport f r,∃S : Finset (Fin r),∃z : Word r,
      1≤S.card ∧ S.card≤3 ∧ ¬Affine (minor D S z) := by
  obtain ⟨r,⟨D⟩⟩:=systematic f closed nonzero
  obtain ⟨S,hS,z,hz⟩:=OrdinaryNegativeAffineThreeFaces.exists_bad_face
    D.reduced D.reduced_full (nonAffine_reduced D bad)
  have hbad:¬Affine (minor D S z):=fun h=>hz (face_affine_of_minor D S z h)
  exact ⟨r,D,S,z,rank_positive (minorChart D S z) hbad,hS,hbad⟩

variable {K : IntermediateField ℚ AlgebraicComplex}

/-- An unchanged original-field row with an actual pure pin map, selected
rank one, two, or three, and all further proper information faces Affine. -/
theorem exists_minimal (f : Signature K n)
    (closed : C.Closed (fun x=>(f x : AlgebraicComplex))) (nonzero : f≠0)
    (bad : ¬Affine (fun x=>(f x : AlgebraicComplex))) :
    ∃rank : ℕ,1≤rank ∧ rank≤3 ∧ ∃W : PinWitness f rank,
      ∀S : Finset (Fin rank),S.card<rank → ∀z : Word rank,Affine (minor W.chart S z) := by
  classical
  let F : Signature AlgebraicComplex n:=fun x=>(f x : AlgebraicComplex)
  have hn:F≠0:=by
    intro hz
    apply nonzero
    funext x
    exact Subtype.ext (congrFun hz x)
  obtain ⟨r,D,S,z,lo,hi,hbad⟩:=exists_low_rank F closed hn bad
  let p:=substitution (remaining D S) (D.encode z)
  have he:row f p=minor D S z:=(literal_substitution F _ _).symm
  let initial : PinWitness f S.card:={
    arity:=(remaining D S).card
    pins:=p
    pure:=substitution_unique _ _
    chart:=by rw [he];exact minorChart D S z
    bad:=by rwa [he] }
  have existsRank:∃j : ℕ,Nonempty (PinWitness f j):=⟨S.card,⟨initial⟩⟩
  let rank:=Nat.find existsRank
  obtain ⟨W⟩:=Nat.find_spec existsRank
  have upper:rank≤3:=le_trans (Nat.find_min' existsRank ⟨initial⟩) hi
  refine ⟨rank,rank_positive W.chart W.bad,upper,W,?_⟩
  intro S smaller z
  by_contra ha
  exact Nat.find_min existsRank smaller ⟨W.smaller S z ha⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureClosedMinimal
end
