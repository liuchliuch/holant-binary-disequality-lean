import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixPacked
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixMatchingCoordinates

/-! The packed integer test accepts every bounded real Pauli matching.
Its original real multiplier is recovered as an actual integer coefficient;
the finite source and every Bell probe satisfy the required bound internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixPackedSafety
open Holant Holant.Tractable Holant.Algebraic
namespace D
export GlobalCloseCompletionKleinSixFiniteData (line source card sign)
end D
namespace P
export GlobalCloseCompletionKleinSixPacked (safe dictionary_correct)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
def first : Fin 48→Fin 16 := ![0,1,0,1,4,5,4,5,0,1,0,1,4,5,4,5,0,1,0,1,2,3,2,3,0,1,0,1,2,3,2,3,0,2,0,2,1,3,1,3,0,2,0,2,1,3,1,3]

theorem first_value : ∀a : Fin 48,D.line a (first a)=1 := by decide +kernel

theorem line_bounds (a : Fin 48) (x : Fin 16) : -1≤D.line a x ∧ D.line a x≤1 := by
  unfold D.line
  split_ifs <;> norm_num

theorem signed_bounds (s : Fin 8) (k : ℕ) (a : Fin 48) (x : Fin 16) :
    -1≤D.sign s k*D.line a x ∧ D.sign s k*D.line a x≤1 := by
  have h := line_bounds a x
  unfold D.sign
  split_ifs <;> constructor <;> nlinarith

theorem source_bounds (a b c : Fin 48) (s : Fin 8) (w : Fin 64) :
    -2≤D.source a b c s w ∧ D.source a b c s w≤2 := by
  let i : Fin 16 := ⟨w.val%16,Nat.mod_lt _ (by decide)⟩
  have h0 := line_bounds 0 i
  have h1 := signed_bounds s 0 a i
  have h2 := signed_bounds s 1 b i
  have h3 := signed_bounds s 2 c i
  unfold D.source
  change -2≤(if w.val<16 then D.line 0 i+D.sign s 1*D.line b i
    else if w.val<32 then D.sign s 0*D.line a i+D.sign s 2*D.line c i
    else if w.val<48 then D.sign s 0*D.line a i-D.sign s 2*D.line c i
    else D.line 0 i-D.sign s 1*D.line b i) ∧ _
  split_ifs <;> constructor <;> linarith

theorem pauli_bounds (z : Fin 4→ℤ) (bound : ∀i,-2≤z i ∧ z i≤2) (k : Fin 4) :
    -4≤(∑t : Fin 4,GlobalCloseCompletionKleinGramCertificate.pauli k
      (GlobalCloseCompletionKleinGramCertificate.word t 0)
      (GlobalCloseCompletionKleinGramCertificate.word t 1)*z t) ∧
    (∑t : Fin 4,GlobalCloseCompletionKleinGramCertificate.pauli k
      (GlobalCloseCompletionKleinGramCertificate.word t 0)
      (GlobalCloseCompletionKleinGramCertificate.word t 1)*z t)≤4 := by
  have h0 := bound 0
  have h1 := bound 1
  have h2 := bound 2
  have h3 := bound 3
  fin_cases k <;> norm_num [GlobalCloseCompletionKleinGramCertificate.pauli,
    GlobalCloseCompletionKleinGramCertificate.word,Fin.sum_univ_succ] <;>
    constructor <;> linarith

theorem card_bounds (a b c : Fin 48) (s : Fin 8) (j k : Fin 4) (x : Fin 16) :
    -4≤D.card a b c s j k x ∧ D.card a b c s j k x≤4 :=
  pauli_bounds _ (fun _=>source_bounds a b c s _) k

theorem safe_of_coordinates (q : Fin 16→ℤ) (bound : ∀x,-4≤q x ∧ q x≤4)
    (a : Fin 48) (c : ℝ) (equation : ∀x,(q x:ℝ)=c*(D.line a x:ℝ)) : P.safe q=true := by
  have atFirst := equation (first a)
  rw [first_value,Int.cast_one,mul_one] at atFirst
  have integral (x : Fin 16) : q x=q (first a)*D.line a x := by
    have h := equation x
    rw [←atFirst] at h
    exact_mod_cast h
  have lower : 0≤q (first a)+4 := by have h:=bound (first a);omega
  have upper : q (first a)+4<9 := by have h:=bound (first a);omega
  let d : Fin 9 := ⟨(q (first a)+4).toNat,by omega⟩
  have scale : (d.val:ℤ)-4=q (first a) := by
    dsimp [d]
    rw [Int.toNat_of_nonneg lower]
    ring
  have table : q=fun x=>((d.val:ℤ)-4)*D.line a x := by
    funext x
    rw [scale]
    exact integral x
  rw [table]
  exact P.dictionary_correct a d


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixPackedSafety
end
