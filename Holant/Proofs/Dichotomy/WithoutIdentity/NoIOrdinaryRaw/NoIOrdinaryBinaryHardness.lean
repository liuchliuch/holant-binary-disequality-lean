import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryBinaryRecipes
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryConjugate
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralFullBinarySupply
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryFiniteValues
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Full non-Affine/non-Product even binary resources are hard without a
supplied sign. Finite coefficient powers physically supply a conjugate Gram;
its unequal norms force the diagonal interpolation source internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryBinaryHardness
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
namespace R
export NoIOrdinaryBinaryRecipes (candidate candidateBlock candidate_value gramBlock gram_value gramPower)
end R
namespace C
export NoIOrdinaryConjugate (gram normTable positive_power good_nonproduct gram_full gram_not_flat)
end C
namespace P
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlanePositive
  (Good candidate choice nontract_positive a b c d)
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneTract (lift_tract_iff)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option Elab.async false

theorem candidate_norm (f : Signature ℂ 2) (i : Fin 5) :
    C.normTable (R.candidate f i)=P.candidate (f ![false,false]) (f ![false,true]) (f ![true,false]) (f ![true,true]) i := by
  fin_cases i <;> rfl

theorem candidate_map {K : Type} [Field K] (phi : K→+*ℂ) (f : Signature K 2) (i : Fin 5) (x : Fin 2→Bool) :
    phi (R.candidate f i x)=R.candidate (fun z=>phi (f z)) i x := by
  fin_cases i <;> simp [R.candidate,map_mul,map_add,map_pow]

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
def phi : src.K→+*ℂ := (algebraicClosure ℚ ℂ).subtype.comp src.K.subtype
def ambient (row : B.Block (s:=src.size) (b:=src.b) 2) : Signature AlgebraicComplex 2:=
  fun x=>(row.signature src.H x : AlgebraicComplex)
def complex (row : B.Block (s:=src.size) (b:=src.b) 2) : Signature ℂ 2:=
  fun x=>phi G src (row.signature src.H x)

theorem candidate_complex (row : B.Block (s:=src.size) (b:=src.b) 2) (i : Fin 5) :
    complex G src (R.candidateBlock row i)=R.candidate (complex G src row) i := by
  funext x
  rw [complex,R.candidate_value,candidate_map]
  rfl

theorem gram_complex (row : B.Block (s:=src.size) (b:=src.b) 2) (k : ℕ) (c : ℂ)
    (conjugate : ∀x,complex G src row x^k=c*star (complex G src row x)) :
    complex G src (R.gramBlock row k)=fun x=>c*C.gram (complex G src row) x := by
  funext x
  rw [complex,R.gram_value]
  change phi G src (∑v : Bool,row.signature src.H ![x 0,v]*row.signature src.H ![x 1,v]^k)=_
  simp only [map_sum,map_mul,map_pow]
  change (∑v : Bool,complex G src row ![x 0,v]*complex G src row ![x 1,v]^k)=_
  simp_rw [conjugate]
  rw [C.gram,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

variable (row : B.Block (s:=src.size) (b:=src.b) 2)
variable (full : ∀x,row.signature src.H x≠0)
variable (badA : ¬Affine (ambient G src row)) (badP : ¬Product (ambient G src row))
variable (negative : ¬Tract (NoIOrdinaryRaw.GenericOrdinarySource.family G src))

include full badA badP negative in
theorem countingHard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  by_contra noHard
  have fullA : ∀x,ambient G src row x≠0:=fun x=>(map_ne_zero (src.K.val.toRingHom : src.K→+*AlgebraicComplex)).mpr (full x)
  have rejected : ¬EOTract {⟨4,Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCore.lift (ambient G src row)⟩} := by
    intro good
    exact (P.lift_tract_iff (ambient G src row)).mp good |>.elim badA badP
  let i:=P.choice (P.a (ambient G src row)) (P.b (ambient G src row))
    (P.c (ambient G src row)) (P.d (ambient G src row))
  have good : P.Good (C.normTable (R.candidate (complex G src row) i)) := by
    rw [candidate_norm]
    exact P.nontract_positive (ambient G src row) fullA rejected
  let q:=R.candidateBlock row i
  have goodQ : P.Good (C.normTable (complex G src q)) := by
    rw [candidate_complex]
    exact good
  have badQ : ¬Product (ambient G src q):=C.good_nonproduct (ambient G src q) goodQ
  have fullQ:=NoIOrdinaryRaw.NoXGeneralFullBinarySupply.full G src noHard q badQ
  obtain ⟨n,hn,powers⟩:=NoIOrdinaryRaw.NoIOrdinaryFiniteValues.binary G src row full badA badP negative noHard q fullQ
  have complexPowers : ∀x,complex G src q x^n=complex G src q ![false,false]^n := by
    intro x
    exact (map_pow (phi G src) _ n).symm.trans ((congrArg (phi G src) (powers x)).trans (map_pow (phi G src) _ n))
  have fullComplex : ∀x,complex G src q x≠0:=fun x=>(map_ne_zero (phi G src)).mpr (fullQ x)
  obtain ⟨c,hc,conjugate⟩:=C.positive_power (complex G src q) fullComplex n hn complexPowers
  let h:=R.gramBlock q (n-1)
  have value:=gram_complex G src q (n-1) c conjugate
  have fullH : ∀x,h.signature src.H x≠0 := by
    intro x zero
    have live:=mul_ne_zero hc (C.gram_full (complex G src q) goodQ x)
    apply live
    rw [←congrFun value x]
    change phi G src (h.signature src.H x)=0
    rw [zero,map_zero]
  obtain ⟨m,hm,hpowers⟩:=NoIOrdinaryRaw.NoIOrdinaryFiniteValues.binary G src row full badA badP negative noHard h fullH
  apply C.gram_not_flat (complex G src q) goodQ
  intro x
  have cp : complex G src h x^m=complex G src h ![false,false]^m:=
    (map_pow (phi G src) _ m).symm.trans ((congrArg (phi G src) (hpowers x)).trans (map_pow (phi G src) _ m))
  have norms:=NoIOrdinaryRaw.NoIOrdinaryFiniteValues.complex_norm_of_power (by omega : m≠0) cp
  rw [congrFun value x,congrFun value ![false,false],Complex.normSq_mul,Complex.normSq_mul] at norms
  exact mul_left_cancel₀ (Complex.normSq_pos.mpr hc).ne' norms

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryBinaryHardness
end
