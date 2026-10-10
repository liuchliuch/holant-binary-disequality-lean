import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreeParity
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineCharacters
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsSource

/-! Signed physical port names of a rank-three support chart. Character maps
appear only as affine semantic pullbacks: every emitted row is an actual
constant/signed-identification substitution into the original signature. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankThreePorts
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.FlatNetwork
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSignedPortsCore
open scoped BigOperators
namespace P
export OrdinaryNegativeSparseRankThreeParity (name value Transform inputs image linearWord image_value)
end P
namespace A
export OrdinaryNegativeSparseMixingAlpha (codeSeven codeSeven_affine)
end A
namespace C
export OrdinaryNegativeAffineCharacters (coordinate_vector mask)
end C
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false

variable {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 3)

def rawName (i : Fin n) : Fin 8 :=
  let a := D.encode (origin 3) i
  P.name (a ^^ D.encode (basis 0) i) (a ^^ D.encode (basis 1) i) (a ^^ D.encode (basis 2) i)

def port (i : Fin n) : Port 7 :=
  if h : rawName D i=0 then .inl (D.encode (origin 3) i)
  else .inr (⟨(rawName D i).val-1,by have hlt:=(rawName D i).isLt;have hn:=(rawName D i).pos_iff_ne_zero.mpr h;omega⟩,
    D.encode (origin 3) i)

theorem rawName_value (i : Fin n) (x : Fin 3→Bool) :
    Bool.xor (D.encode (origin 3) i) (P.value (rawName D i) x)=D.encode x i := by
  apply boolEquiv.injective
  change bitValue (ZMod 2) (D.encode (origin 3) i ^^ P.value (rawName D i) x)=
    bitValue (ZMod 2) (D.encode x i)
  rw [C.coordinate_vector D i x]
  cases ha : D.encode (origin 3) i <;>
    cases hb : D.encode (basis 0) i <;> cases hc : D.encode (basis 1) i <;>
    cases hd : D.encode (basis 2) i <;>
    cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hx2 : x 2 <;>
    norm_num [rawName,P.name,P.value,A.codeSeven,C.mask,TwoTranslate.dot,
      Fin.sum_univ_three,bitValue,ha,hb,hc,hd,hx0,hx1,hx2]
  all_goals decide

theorem word_code (x : Fin 3→Bool) : OrdinaryNegativeSignedPortsCore.word (port D) (A.codeSeven x)=D.encode x := by
  funext i
  rw [←rawName_value D i x]
  simp only [OrdinaryNegativeSignedPortsCore.word,port]
  split_ifs with h
  · simp [OrdinaryNegativeSignedPortsCore.word,P.value,h]
  · simp [OrdinaryNegativeSignedPortsCore.word,P.value,h]

/-- Transform the physical name only; a zero transformed name becomes a
literal pin to that original port's supported base bit. -/
def transformed (p : Fin n→Port 7) (t : P.Transform) (i : Fin n) : Port 7 :=
  match p i with
  | .inl b=>.inl b
  | .inr (j,s)=>if h : P.image t j=0 then .inl s else
      .inr (⟨(P.image t j).val-1,by have hlt:=(P.image t j).isLt;have hn:=(P.image t j).pos_iff_ne_zero.mpr h;omega⟩,s)

theorem transformed_word (p : Fin n→Port 7) (t : P.Transform) (x : Fin 3→Bool) :
    OrdinaryNegativeSignedPortsCore.word (transformed p t) (A.codeSeven x)=OrdinaryNegativeSignedPortsCore.word p (A.codeSeven (P.linearWord t x)) := by
  funext i
  simp only [OrdinaryNegativeSignedPortsCore.word,transformed]
  cases h : p i with
  | inl b=>simp [h]
  | inr v=>
      rcases v with ⟨j,s⟩
      have hv := P.image_value t j x
      simp only [h]
      
      split_ifs with hz
      · simp [P.value,hz] at hv
        simp [OrdinaryNegativeSignedPortsCore.word,h,hv]
      · simpa [OrdinaryNegativeSignedPortsCore.word,h,P.value,hz] using congrArg (fun b=>s ^^ b) hv

theorem transformed_code (t : P.Transform) (x : Fin 3→Bool) :
    OrdinaryNegativeSignedPortsCore.word (transformed (port D) t) (A.codeSeven x)=D.encode (P.linearWord t x) := by
  rw [transformed_word,word_code]

/-- Exact finite sum of unchanged original bundle counts, before parity. -/
theorem transformed_count (p : Fin n→Port 7) (t : P.Transform) (j : Fin 7) :
    I.bundleSize (transformed p t) j=
      ∑k : Fin 7,if P.image t k=j.succ then I.bundleSize p k else 0 := by
  unfold I.bundleSize
  have distribute (h : Prop) [Decidable h] (g : Fin n→ℕ) :
      (if h then ∑i,g i else 0)=∑i,if h then g i else 0 := by
    split_ifs <;> simp
  simp_rw [distribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases hp : p i with
  | inl b=>simp [transformed,hp]
  | inr v=>
      rcases v with ⟨k,s⟩
      have he (v : Fin 8) (h : v≠0) : (⟨v.val-1,by omega⟩ : Fin 7)=j ↔ v=j.succ := by
        constructor <;> intro hh <;> apply Fin.ext
        · have hv := congrArg Fin.val hh
          have hn := v.pos_iff_ne_zero.mpr h
          simp only [Fin.val_mk,Fin.val_succ] at hv ⊢
          omega
        · have hv := congrArg Fin.val hh
          simp only [Fin.val_mk,Fin.val_succ] at hv ⊢
          omega
      have hs : j.succ≠(0 : Fin 8) := Fin.succ_ne_zero j
      simp only [hp]
      rw [Finset.sum_eq_single k]
      · simp only [ite_true]
        by_cases hz : P.image t k=0
        · simp [transformed,hp,hz,Ne.symm hs]
        · simp [transformed,hp,hz,he _ hz]
      · intro v _ hv
        simp [hv,Ne.symm hv]
      · simp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankThreePorts
end
