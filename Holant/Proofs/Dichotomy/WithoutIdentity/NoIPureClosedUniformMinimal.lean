import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureClosedMinimal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparsePinProduct

/-! Arbitrary nonzero uniform phases commute with actual original pure pins.
Closed-support minimum-rank descent retains the original coefficient row and
the exact nonzero scalar contributed by pinned coordinates. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureClosedUniformMinimal
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
open OrdinaryNegativeSparseMinimalRank OrdinaryNegativeSparsePinTwist
open scoped BigOperators
namespace C
export NoIPureClosedMinimal.C (Closed)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
variable {n m r : ℕ}

def twist (a : AlgebraicComplex) (f : Signature AlgebraicComplex n) : Signature AlgebraicComplex n:=
  fun x=>a^(Holant.weight x)*f x

theorem pow_weight (a : AlgebraicComplex) (x : Word n) :
    a^(Holant.weight x)=∏i,if x i then a else 1 := by
  unfold Holant.weight
  rw [←Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> simp

theorem twist_support (a : AlgebraicComplex) (ha : a≠0)
    (f : Signature AlgebraicComplex n) (x : Word n) : twist a f x≠0 ↔ f x≠0 := by
  simp only [twist,mul_ne_zero_iff,and_iff_right (pow_ne_zero _ ha)]

def pinScalar (a : AlgebraicComplex) (p : Fin n→Bool ⊕ Fin m) : AlgebraicComplex:=
  fixedProduct p (fun b=>if b then a else 1)

theorem pinScalar_nonzero (a : AlgebraicComplex) (ha : a≠0)
    (p : Fin n→Bool ⊕ Fin m) : pinScalar a p≠0 := by
  unfold pinScalar fixedProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro b _
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  cases b <;> simp [ha]

theorem twist_pin (a : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (p : Fin n→Bool ⊕ Fin m) (hp : PurePins p) :
    (fun x=>twist a f (T.substitute p x))=
      fun x=>pinScalar a p*twist a (fun y=>f (T.substitute p y)) x := by
  funext x
  simp only [twist,pow_weight]
  rw [product_pure p hp (fun b=>if b then a else 1) x]
  exact mul_assoc _ _ _

theorem twist_pin_affine_iff (a : AlgebraicComplex) (ha : a≠0)
    (f : Signature AlgebraicComplex n) (p : Fin n→Bool ⊕ Fin m) (hp : PurePins p) :
    Affine (fun x=>twist a f (T.substitute p x)) ↔
      Affine (twist a (fun y=>f (T.substitute p y))) := by
  rw [twist_pin a f p hp]
  constructor
  · intro h
    convert h.scale (pinScalar a p)⁻¹ using 1
    funext x
    rw [←mul_assoc,inv_mul_cancel₀ (pinScalar_nonzero a ha p),one_mul]
  · intro h
    exact h.scale (pinScalar a p)

def supportChart {g h : Signature AlgebraicComplex n} (D : SystematicSupport g r)
    (support : ∀x,g x≠0 ↔ h x≠0) : SystematicSupport h r where
  ports:=D.ports
  injective:=D.injective
  encode:=D.encode
  affine:=D.affine
  free:=D.free
  supported x:=(support _).mp (D.supported x)
  covers x hx:=D.covers x ((support x).mpr hx)

def twistChart (a : AlgebraicComplex) (ha : a≠0)
    {f : Signature AlgebraicComplex n} (D : SystematicSupport f r) :
    SystematicSupport (twist a f) r:=supportChart D (fun x=>(twist_support a ha f x).symm)

theorem twist_closed (a : AlgebraicComplex) (ha : a≠0)
    {f : Signature AlgebraicComplex n} (closed : C.Closed f) : C.Closed (twist a f) := by
  intro x y z hx hy hz
  exact (twist_support a ha f _).mpr (closed x y z
    ((twist_support a ha f x).mp hx) ((twist_support a ha f y).mp hy)
    ((twist_support a ha f z).mp hz))

theorem twist_minor_affine_iff (a : AlgebraicComplex) (ha : a≠0)
    {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)
    (S : Finset (Fin r)) (z : Word r) :
    Affine (minor (twistChart a ha D) S z) ↔ Affine (twist a (minor D S z)) := by
  change Affine (literal (twist a f) (remaining D S) (D.encode z)) ↔
    Affine (twist a (literal f (remaining D S) (D.encode z)))
  rw [literal_substitution,literal_substitution]
  exact twist_pin_affine_iff a ha f _ (substitution_unique _ _)

variable {K : IntermediateField ℚ AlgebraicComplex}

structure UniformPinWitness (a : AlgebraicComplex) (f : Signature K n) (rank : ℕ) where
  arity : ℕ
  pins : Fin n→Bool ⊕ Fin arity
  pure : PurePins pins
  chart : SystematicSupport (row f pins) rank
  bad : ¬Affine (twist a (row f pins))

namespace UniformPinWitness
variable {a : AlgebraicComplex} {f : Signature K n} {rank : ℕ}
variable (W : UniformPinWitness a f rank)

def facePins (S : Finset (Fin rank)) (z : Word rank) :
    Fin n→Bool ⊕ Fin (remaining W.chart S).card:=
  I.compose W.pins (substitution (remaining W.chart S) (W.chart.encode z))

theorem facePins_pure (S : Finset (Fin rank)) (z : Word rank) : PurePins (W.facePins S z):=
  pure_compose _ _ W.pure (substitution_unique _ _)

theorem facePins_value (S : Finset (Fin rank)) (z : Word rank) :
    row f (W.facePins S z)=minor W.chart S z := by
  funext x
  simp only [row,facePins,I.substitute_compose]
  exact (congrFun (literal_substitution (row f W.pins)
    (remaining W.chart S) (W.chart.encode z)) x).symm

def smaller (S : Finset (Fin rank)) (z : Word rank)
    (bad : ¬Affine (twist a (minor W.chart S z))) : UniformPinWitness a f S.card where
  arity:=(remaining W.chart S).card
  pins:=W.facePins S z
  pure:=W.facePins_pure S z
  chart:=by rw [W.facePins_value];exact minorChart W.chart S z
  bad:=by rwa [W.facePins_value]

theorem affine_face_precompose (ha : a≠0) {m : ℕ} (S : Finset (Fin rank)) (z : Word rank)
    (h : Affine (twist a (minor W.chart S z))) (q : Word m→Word rank)
    (hq : IsAffineMap q) (fixed : ∀x i,i∉S → q x i=z i) :
    Affine (fun x=>twist a (row f W.pins) (W.chart.encode (q x))) := by
  have hcut:Affine (minor (twistChart a ha W.chart) S z):=
    (twist_minor_affine_iff a ha W.chart S z).mpr h
  have pull:=(face_affine_of_minor (twistChart a ha W.chart) S z hcut).precompose q hq
  convert pull using 1
  funext x
  exact (ite_eq_left (fixed x)).symm

theorem affine_of_fixed_coordinate (ha : a≠0)
    (minimal : ∀S : Finset (Fin rank),S.card<rank → ∀z : Word rank,
      Affine (twist a (minor W.chart S z))) {m : ℕ}
    (q : Word m→Word rank) (hq : IsAffineMap q) (j : Fin rank) (b : Bool)
    (fixed : ∀x,q x j=b) :
    Affine (fun x=>twist a (row f W.pins) (W.chart.encode (q x))) := by
  let S : Finset (Fin rank):=Finset.univ.erase j
  have smaller:S.card<rank:=by
    simpa [S] using Finset.card_erase_lt_of_mem (Finset.mem_univ j)
  apply W.affine_face_precompose ha S (fun _=>b) (minimal S smaller (fun _=>b)) q hq
  intro x i hi
  have he:i=j:=by simpa [S] using hi
  subst i
  exact fixed x

end UniformPinWitness

/-- Semantic twisting may use any nonzero scalar. The returned witness is
still a pure pinning of the unchanged original coefficient-field row. -/
theorem exists_minimal_uniform (a : AlgebraicComplex) (ha : a≠0) (f : Signature K n)
    (closed : C.Closed (fun x=>(f x : AlgebraicComplex))) (nonzero : f≠0)
    (bad : ¬Affine (twist a (fun x=>(f x : AlgebraicComplex)))) :
    ∃rank : ℕ,1≤rank ∧ rank≤3 ∧ ∃W : UniformPinWitness a f rank,
      ∀S : Finset (Fin rank),S.card<rank → ∀z : Word rank,
        Affine (twist a (minor W.chart S z)) := by
  classical
  let F : Signature AlgebraicComplex n:=fun x=>(f x : AlgebraicComplex)
  have hn:twist a F≠0:=by
    intro hz
    apply nonzero
    funext x
    apply Subtype.ext
    by_contra h
    exact (twist_support a ha F x).mpr h (congrFun hz x)
  obtain ⟨r,D,S,z,lo,hi,hbad⟩:=NoIPureClosedMinimal.exists_low_rank
    (twist a F) (twist_closed a ha closed) hn bad
  let p:=substitution (remaining D S) (D.encode z)
  have he:(fun x=>twist a F (T.substitute p x))=minor D S z:=
    (literal_substitution (twist a F) _ _).symm
  let chartTwisted:SystematicSupport (fun x=>twist a F (T.substitute p x)) S.card:=by
    rw [he];exact minorChart D S z
  let chartOriginal:SystematicSupport (row f p) S.card:=
    supportChart chartTwisted (fun x=>twist_support a ha F (T.substitute p x))
  have hb:¬Affine (twist a (row f p)):=by
    intro h
    apply hbad
    rw [←he]
    exact (twist_pin_affine_iff a ha F p (substitution_unique _ _)).mpr h
  let initial:UniformPinWitness a f S.card:=
    ⟨(remaining D S).card,p,substitution_unique _ _,chartOriginal,hb⟩
  have existsRank:∃j : ℕ,Nonempty (UniformPinWitness a f j):=⟨S.card,⟨initial⟩⟩
  let rank:=Nat.find existsRank
  obtain ⟨W⟩:=Nat.find_spec existsRank
  have upper:rank≤3:=le_trans (Nat.find_min' existsRank ⟨initial⟩) hi
  have lower:1≤rank:=NoIPureClosedMinimal.rank_positive (twistChart a ha W.chart) W.bad
  refine ⟨rank,lower,upper,W,?_⟩
  intro S smaller z
  by_contra h
  exact Nat.find_min existsRank smaller ⟨W.smaller S z h⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureClosedUniformMinimal
end
