import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryGraphRankOneLocal
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOneUniform
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryEvenHardness
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralOddAnti
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! A genuine LocalAffine-bad rank-one row supplies a standard Affine or
alpha-Affine odd unary resource. The apparent overlap of its two Affine
classes is discharged by its actual separately odd anti projection. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryLocalRankOneSupply
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport
namespace A
export OrdinaryNegativeAffineRankOne.SystematicSupport (left right left_supported right_supported supported_words
  affine_iff_fourth uniform_iff_signed_fourth)
export OrdinaryNegativeAffineRankOne (sign sign_sq sign_distance uniform)
end A
namespace P
export NoXReciprocalSelectionRankOne (ports)
export NoXSeparateSignedProjection (signedCount)
export NoXReciprocalSelectionRankOnePins (minor resource anti)
export NoXReciprocalSelectionRankOneDistance (counts)
end P
namespace W
export NoXWeightedRankOneCore (negativeCount)
export NoXLocalRankOneWeighted (local_iff_even_sign negativeSign_pow)
end W
namespace R
export OrdinaryNegativeXUniversalResource (AlphaResource AffineResource EvenBad)
export NoXReciprocalSelectionRankOneSupply (OddAnti)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false

theorem negative_count {n : ℕ} (x y : Fin n→Bool) :
    W.negativeCount x y=P.signedCount (P.ports x y) 0 true:=by
  unfold W.negativeCount P.signedCount
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> cases hy : y i <;> simp [P.ports,OrdinaryNegativeRankOneCore.neg,hx,hy]

theorem dual_even {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 1)
    (square : Affine (fun x=>f x^2)) (good : Affine f) (uniform : Affine (A.uniform f)) :
    Even (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance.distance (A.left D) (A.right D)):=by
  have equal:=(A.affine_iff_fourth D square).mp good
  have signs:=(A.uniform_iff_signed_fourth D square).mp uniform
  rw [equal] at signs
  have same:=mul_right_cancel₀ (pow_ne_zero 4 (A.right_supported D)) signs
  have one:=A.sign_distance (A.left D) (A.right D)
  rw [←same,←pow_two,A.sign_sq] at one
  rcases Nat.even_or_odd (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance.distance
    (A.left D) (A.right D)) with he|ho
  · exact he
  · rw [ho.neg_one_pow] at one
    norm_num at one

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
variable (j : Fin src.size) (D : SystematicSupport (fun x=>(src.H j x : AlgebraicComplex)) 1)
variable (square : Affine (fun x=>(src.H j x : AlgebraicComplex)^2))
variable (bad : ¬LocalAffine (fun x=>(src.H j x : AlgebraicComplex)))

include D negative square bad in
theorem dual_hard (good : Affine (fun x=>(src.H j x : AlgebraicComplex)))
    (uniform : Affine (A.uniform (fun x=>(src.H j x : AlgebraicComplex)))) :
    NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G:=by
  let x:=A.left D
  let y:=A.right D
  have even:=dual_even D square good uniform
  have en : ¬Even (W.negativeCount x y):=by
    intro evenNeg
    apply bad
    apply (W.local_iff_even_sign D square).mpr
    refine ⟨even,?_⟩
    rw [W.negativeSign_pow,evenNeg.neg_one_pow,one_mul]
    exact (A.affine_iff_fourth D square).mp good
  have on : Odd (P.signedCount (P.ports x y) 0 true):=by
    rw [←negative_count]
    exact Nat.not_even_iff_odd.mp en
  have op : Odd (P.signedCount (P.ports x y) 0 false):=by
    rw [P.counts] at even
    apply Nat.not_even_iff_odd.mp
    intro ep
    exact Nat.not_even_iff_odd.mpr on ((Nat.even_add.mp even).mp ep)
  have odd : ∀q bit,Odd (P.signedCount (P.ports x y) q bit):=by
    intro q bit
    have hq:q=0:=Fin.eq_zero q
    subst q
    cases bit
    · exact op
    · exact on
  have pure : OrdinaryNegativeSparseMinimalRank.PurePins (Sum.inr : Fin (src.b j.val)→Bool ⊕ Fin (src.b j.val)):=by
    intro i
    refine ⟨i,rfl,?_⟩
    intro k eqn
    exact Sum.inr.inj eqn
  have support : ∀z,P.minor src.H j Sum.inr z≠0→z=x ∨ z=y:=by
    intro z hz
    exact A.supported_words D z (fun h=>hz (Subtype.ext h))
  exact NoIOrdinaryRaw.NoXGeneralOddAnti.countingHard G src
    (P.resource src.H j (src.p false) (src.p true) (src.hp false) (src.hp true) Sum.inr pure x y odd)
    (src.H j x) (src.H j y)
    (fun h=>A.left_supported D (congrArg Subtype.val h))
    (fun h=>A.right_supported D (congrArg Subtype.val h))
    (P.anti src.H j (src.p false) (src.p true) (src.hp false) (src.hp true) Sum.inr pure x y odd support)
    negative

include D negative square bad in
theorem label (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G) :
    Nonempty (R.AlphaResource src.H .one) ∨ Nonempty (R.AffineResource src.H .one):=by
  have noBad : ¬R.EvenBad src.H:=fun h=>noHard (NoIOrdinaryRaw.NoIOrdinaryEvenHardness.countingHard G src negative h)
  have noAnti : ¬R.OddAnti src.H:=by
    rintro ⟨T,v,w,hv,hw,eqn⟩
    exact noHard (NoIOrdinaryRaw.NoXGeneralOddAnti.countingHard G src T v w hv hw eqn negative)
  by_cases good : Affine (fun x=>(src.H j x : AlgebraicComplex))
  · have failure : ¬Affine (A.uniform (fun x=>(src.H j x : AlgebraicComplex))):=
      fun h=>noHard (dual_hard G src negative j D square bad good h)
    let V : OrdinaryNegativeSparseUniformMinimal.UniformPinWitness (src.H j) 1:=
      ⟨src.b j.val,Sum.inr,(by intro i;refine ⟨i,rfl,?_⟩;intro k eqn;exact Sum.inr.inj eqn),D,failure⟩
    exact Or.inr (((NoXReciprocalSelectionRankOneUniform.uniform src.H j (src.p false) (src.p true)
      (src.hp false) (src.hp true) V square).resolve_left noBad).resolve_left noAnti)
  · have supplied:=NoXReciprocalSelectionRankOneSupply.ordinary src.H j (src.p false) (src.p true)
      (src.hp false) (src.hp true) (NoIOrdinaryRaw.NoIOrdinaryGraphRankOneLocal.selfWitness (src.H j) D good) square
    exact Or.inl ((supplied.resolve_left noBad).resolve_left noAnti)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryLocalRankOneSupply
end
