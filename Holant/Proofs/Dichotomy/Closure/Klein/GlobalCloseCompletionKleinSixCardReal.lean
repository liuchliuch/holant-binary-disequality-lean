import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixBellNorm
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinStandardRealLine

/-! Exact real scalar of every actual first-pair Pauli card. The ordinary
Bell coordinate has its unnormalized factor two; the actual raw-card row keeps
both the original source scalar and its original-field dual correction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixCardReal
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
namespace B
export GlobalCloseCompletionKleinSixBellNorm (card matrix)
end B
namespace N
export GlobalCloseCompletionKleinGramNorm (rows)
end N
namespace W
export GlobalCloseCompletionKleinGramCertificate (word)
end W
namespace H
export GlobalCloseCompletionKleinH6RMBell (E bell)
end H
namespace K
export Holant.Certificates.EqualityQuaternary.Klein (dual dualQ matrix embed_apply qHalf)
end K
namespace R
export RingHomRealization (mapSignature)
end R
abbrev inclusion : AlgebraicComplex→+*ℂ := CyclicBoundary.AlgebraicRepresentatives.inclusion
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

theorem add_cons (u : Fin 2→Bool) (z : Fin 4→Bool) :
    (Fin.addCases (m:=2) (n:=4) u z : Fin 6→Bool)=Fin.cons (u 0) (Fin.cons (u 1) z) := by
  funext i
  fin_cases i <;> rfl

theorem card_bool (r : Signature ℝ 6) (k : Fin 4) (z : Fin 4→Bool) :
    B.card r k z=∑a : Bool,∑b : Bool,H.E k a b*r (Fin.cons a (Fin.cons b z)) := by
  have row (i : Fin 4) : N.rows (n:=4) r i z=
      r (Fin.cons (W.word i 0) (Fin.cons (W.word i 1) z)) :=
    congrArg r (add_cons (W.word i) z)
  simp only [B.card,row]
  simp only [B.matrix,W.word,Fin.sum_univ_succ,Fintype.sum_bool]
  norm_num
  ring

theorem dual_real (k : Fin 4) (a b : Bool) :
    inclusion (K.dual .standard k a b)=(1/2:ℂ)*(H.E (K:=ℝ) k a b:ℂ) := by
  fin_cases k <;> cases a <;> cases b <;>
    norm_num [K.dual,K.dualQ,K.matrix,K.embed_apply,K.qHalf,H.E,H.bell,
      QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  all_goals change (2:ℂ)⁻¹=(1:ℂ)/2
  all_goals norm_num

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem canonical (f : Signature (OI.K G) 6) (r : Signature ℝ 6) (c : ℂ)
    (normal : R.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=fun x=>c*(r x:ℂ))
    (k : Fin 4) (x : Fin 4→Bool) :
    inclusion (ClosureKleinCurrent.canonicalCard G P torsion cardinal noncyclic f (Equiv.refl _) k x)=
      (c/2)*(B.card r k x:ℂ) := by
  have point (y : Fin 6→Bool) : inclusion (ClosureSourceRows.embedding G (f y))=c*(r y:ℂ) :=
    congrFun normal y
  simp only [ClosureKleinCurrent.canonicalCard,standard,Signature.contract,map_sum,map_mul,
    Tensor.reindex,Equiv.refl_symm,Equiv.refl_apply,R.mapSignature,dual_real,point,card_bool,
    Complex.ofReal_sum,Complex.ofReal_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

include cardinal noncyclic standard in
theorem raw (f : Signature (OI.K G) 6) (r : Signature ℝ 6) (c : ℂ)
    (normal : R.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=fun x=>c*(r x:ℂ))
    (k : Fin 4) (x : Fin 4→Bool) :
    inclusion (R.mapSignature (ClosureSourceRows.embedding G)
      (rawCard P.family torsion f (ClosureKleinCurrent.cardKey G P torsion cardinal noncyclic (Equiv.refl _) k)) x)=
      ((ClosurePhysicalBridge.complexEmbedding G) (ClosureKleinCurrent.dualCorrection G P torsion cardinal noncyclic k)*c/2)*
        (B.card r k x:ℂ) := by
  have h := congrArg inclusion (congrFun (ClosureKleinCurrent.rawCard_mapped G P torsion cardinal noncyclic f (Equiv.refl _) k) x)
  simp only [Pi.smul_apply,smul_eq_mul,map_mul,canonical G P torsion cardinal noncyclic standard f r c normal] at h
  rw [h]
  change (ClosurePhysicalBridge.complexEmbedding G)
    (ClosureKleinCurrent.dualCorrection G P torsion cardinal noncyclic k)*(c/2*(B.card r k x:ℂ))=_
  ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixCardReal
end
