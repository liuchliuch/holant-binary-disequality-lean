import Holant.Proofs.Closure.ClosureKleinCurrentMatching
import Holant.Proofs.Closure.HistorySectorCards
import Holant.Proofs.Closure.DeckContraction

/-! Canonical all-arity dual cards at every original ordered pair, derived
from literal CURRENT raw keys with exact nonzero ORIGINAL-field corrections.
Zero cards remain zero, and no six/eight classification is an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain

def closingSignSource {L : Type*} [Field L] (k : Fin 4) : L :=
  if k=0 ∨ k=1 then 1 else -1
def dualScalarSource {L : Type*} [Field L] (row : K.Kind) (k : Fin 4) : L :=
  if row=.exotic ∧ ¬(k=0 ∨ k=1) then 1/4 else 1/2

theorem closingSignSource_nonzero {L : Type*} [Field L] (k : Fin 4) :
    closingSignSource (L:=L) k≠0 := by
  unfold closingSignSource
  split_ifs <;> simp
theorem dualScalarSource_nonzero {L : Type*} [Field L] [CharZero L] (row : K.Kind) (k : Fin 4) :
    dualScalarSource (L:=L) row k≠0 := by
  unfold dualScalarSource
  split_ifs <;> norm_num

theorem closingSignSource_mapped {L : Type*} [Field L] (φ : L →+* AlgebraicComplex) (k : Fin 4) :
    φ (closingSignSource (L:=L) k)=K.closingSign k := by
  unfold closingSignSource K.closingSign
  split_ifs <;> simp
theorem dualScalarSource_mapped {L : Type*} [Field L] [CharZero L]
    (φ : L →+* AlgebraicComplex) (row : K.Kind) (k : Fin 4) :
    φ (dualScalarSource (L:=L) row k)=
      EqualityQuaternary.Klein.embed (EqualityQuaternary.Klein.dualScalarQ row k) := by
  cases row <;> fin_cases k <;>
    norm_num [dualScalarSource,EqualityQuaternary.Klein.dualScalarQ,
      EqualityQuaternary.Klein.embed_apply,EqualityQuaternary.Klein.qHalf,
      EqualityQuaternary.Klein.qQuarter,map_div₀]
  all_goals rw [map_ofNat];simp only [one_div]

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))

def dualKey (k : Fin 4) : completeGroup P.family torsion :=
  (index G P torsion cardinal noncyclic (K.theta (kind G P torsion cardinal noncyclic) k)).key
def dualCorrection (k : Fin 4) : OI.K G :=
  (index G P torsion cardinal noncyclic (K.theta (kind G P torsion cardinal noncyclic) k)).coefficient *
    closingSignSource (K.theta (kind G P torsion cardinal noncyclic) k) /
      dualScalarSource (kind G P torsion cardinal noncyclic) k
theorem dualCorrection_nonzero (k : Fin 4) : dualCorrection G P torsion cardinal noncyclic k≠0 :=
  div_ne_zero (mul_ne_zero (index G P torsion cardinal noncyclic _).nonzero
    (closingSignSource_nonzero _)) (dualScalarSource_nonzero _ _)

/-- Literal actual closing matrix and its same recorded original-field unit. -/
theorem dualClosing_mapped (k : Fin 4) :
    (X*actualRepresentative P.family torsion (dualKey G P torsion cardinal noncyclic k)*X).map
      (ClosureSourceRows.embedding G)=
      scale (ClosureSourceRows.embedding G (dualCorrection G P torsion cardinal noncyclic k))
        (K.dual (kind G P torsion cardinal noncyclic) k) := by
  let row := kind G P torsion cardinal noncyclic
  let J := index G P torsion cardinal noncyclic (K.theta row k)
  have normal := J.normal
  have mapped :
      (X*actualRepresentative P.family torsion J.key*X).map (ClosureSourceRows.embedding G)=
      Kernel.mul (Kernel.mul Signature.disequality
        (scale (ClosureSourceRows.embedding G J.coefficient) (K.E row (K.theta row k)))) Signature.disequality := by
    change HistorySectorCards.mapBinary (ClosureSourceRows.embedding G)
      (X*actualRepresentative P.family torsion J.key*X)=_
    rw [HistorySectorCards.map_mul,HistorySectorCards.map_mul,HistorySectorCards.map_X]
    change Kernel.mul (Kernel.mul Signature.disequality
      (ClosureSourceRows.representative G P torsion J.key)) Signature.disequality=_
    rw [normal]
  change (X*actualRepresentative P.family torsion J.key*X).map (ClosureSourceRows.embedding G)=_
  rw [mapped,scale_mul_right,scale_mul_left,K.closing,
    EqualityQuaternary.Klein.dual_scalar]
  funext u v
  change ClosureSourceRows.embedding G J.coefficient *
      (K.closingSign (K.theta row k)*K.E row (K.theta row k) u v)=
    ClosureSourceRows.embedding G
      (J.coefficient*closingSignSource (K.theta row k)/dualScalarSource row k)*
      (EqualityQuaternary.Klein.embed (EqualityQuaternary.Klein.dualScalarQ row k)*
        K.E row (K.theta row k) u v)
  rw [map_div₀,map_mul,closingSignSource_mapped,←dualScalarSource_mapped (ClosureSourceRows.embedding G) row k]
  have hn := (map_ne_zero (ClosureSourceRows.embedding G)).mpr (dualScalarSource_nonzero (L:=OI.K G) row k)
  calc
    _=(ClosureSourceRows.embedding G J.coefficient*K.closingSign (K.theta row k))*
        K.E row (K.theta row k) u v := by ring
    _=((ClosureSourceRows.embedding G J.coefficient*K.closingSign (K.theta row k)/
        ClosureSourceRows.embedding G (dualScalarSource row k))*
        ClosureSourceRows.embedding G (dualScalarSource row k))*K.E row (K.theta row k) u v := by
      rw [div_mul_cancel₀ _ hn]
    _=_ := by ring

variable {n : ℕ} (f : Signature (OI.K G) (n+2))
def cardKey (order : Equiv.Perm (Fin (n+2))) (k : Fin 4) : RawCardKey n (completeGroup P.family torsion) :=
  DeckContraction.orderedKey P.family torsion order (dualKey G P torsion cardinal noncyclic k)
def canonicalCard (order : Equiv.Perm (Fin (n+2))) (k : Fin 4) : Signature AlgebraicComplex n :=
  Signature.contract (K.dual (kind G P torsion cardinal noncyclic) k)
    (Tensor.reindex order.symm (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f))
def normalizedCard (order : Equiv.Perm (Fin (n+2))) (k : Fin 4) : Signature (OI.K G) n :=
  (dualCorrection G P torsion cardinal noncyclic k)⁻¹ •
    rawCard P.family torsion f (cardKey G P torsion cardinal noncyclic order k)

theorem rawCard_mapped (order : Equiv.Perm (Fin (n+2))) (k : Fin 4) :
    RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
      (rawCard P.family torsion f (cardKey G P torsion cardinal noncyclic order k))=
      (ClosureSourceRows.embedding G (dualCorrection G P torsion cardinal noncyclic k)) •
        canonicalCard G P torsion cardinal noncyclic f order k := by
  change HistorySectorCards.RH.mapSignature (ClosureSourceRows.embedding G)
    (rawCard P.family torsion f (cardKey G P torsion cardinal noncyclic order k))=_
  rw [cardKey,DeckContraction.rawCard_ordered,HistorySectorCards.map_contract]
  have matrix := dualClosing_mapped G P torsion cardinal noncyclic k
  change HistorySectorCards.mapBinary (ClosureSourceRows.embedding G) _=_ at matrix
  rw [matrix]
  funext x
  simp only [canonicalCard,Signature.contract,scale,Pi.smul_apply,smul_eq_mul,
    RingHomRealization.mapSignature,Tensor.reindex,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem normalizedCard_mapped (order : Equiv.Perm (Fin (n+2))) (k : Fin 4) :
    RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
      (normalizedCard G P torsion cardinal noncyclic f order k)=
        canonicalCard G P torsion cardinal noncyclic f order k := by
  have scalar := rawCard_mapped G P torsion cardinal noncyclic f order k
  funext x
  change ClosureSourceRows.embedding G
      ((dualCorrection G P torsion cardinal noncyclic k)⁻¹ * rawCard P.family torsion f _ x)=_
  rw [map_mul,map_inv₀]
  have point := congrFun scalar x
  change ClosureSourceRows.embedding G (rawCard P.family torsion f _ x)=
    ClosureSourceRows.embedding G (dualCorrection G P torsion cardinal noncyclic k)*
      canonicalCard G P torsion cardinal noncyclic f order k x at point
  rw [point,←mul_assoc,inv_mul_cancel₀
    ((map_ne_zero _).mpr (dualCorrection_nonzero G P torsion cardinal noncyclic k)),one_mul]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinCurrent
