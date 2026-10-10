import Holant.Complexity.UniversalPairReduction.Surgery.ChoiceSemantics
import Holant.Complexity.UniversalPairReduction.Surgery.Splice

/-! Split one actual edge-choice bit and solve the native-X constraint at a
smoothed binary vertex. These are assignment bijections, not runtime oracles. -/
namespace Holant.Complexity.UniversalPairReduction.Surgery.Choice
open Smoothing

def splitEdge (m e : ℕ) (he : e<m) : (Fin m → Bool) ≃ (Bool × (Fin (m-1) → Bool)) where
  toFun c := (c ⟨e,he⟩,fun j => c ⟨liftEdge e j.val,lift_lt he j.isLt⟩)
  invFun p i := if hi : i.val=e then p.1 else p.2 ⟨lowerEdge e i.val,lower_lt he i.isLt hi⟩
  left_inv c := by
    funext i
    dsimp only
    split_ifs with hi
    · exact congrArg c (Fin.ext hi).symm
    · exact congrArg c (Fin.ext (lift_lower hi))
  right_inv p := by
    apply Prod.ext
    · simp
    · funext j
      simp [lift_ne,lower_lift]

def restore (e : ℕ) (d : Bool) (c : ℕ → Bool) (i : ℕ) : Bool :=
  if i=e then d else c (lowerEdge e i)

 theorem extend_split (m e : ℕ) (he : e<m) (d : Bool) (c : Fin (m-1) → Bool)
    (i : ℕ) (hi : i<m) :
    extend ((splitEdge m e he).symm (d,c)) i=restore e d (extend c) i := by
  unfold extend restore splitEdge
  simp only [Equiv.coe_fn_symm_mk,dif_pos hi]
  by_cases hie : i=e
  · simp [hie]
  · simp [hie,lower_lt he hi hie]

 theorem bit_restore (e : ℕ) (d : Bool) (c : ℕ → Bool) (p : RawEndpoint) (hp : p.1≠e) :
    bit (restore e d c) p=bit c (removeLoopEndpoint e p) := by
  simp [bit,restore,removeLoopEndpoint,hp]
  rfl

 theorem bit_mate (c : ℕ → Bool) (e : ℕ) (b : Bool) : bit c (e,!b)=!(bit c (e,b)) := by
  cases b <;> simp [bit]

def forced (p q : RawEndpoint) (c : ℕ → Bool) : Bool :=
  if q.2 then !(bit c (removeLoopEndpoint q.1 p)) else bit c (removeLoopEndpoint q.1 p)

 theorem bit_forced (p q : RawEndpoint) (c : ℕ → Bool) :
    bit (restore q.1 (forced p q c) c) q = !(bit c (removeLoopEndpoint q.1 p)) := by
  cases hq : q.2 <;> simp [bit,restore,forced,hq]

 theorem bit_splice (p q r : RawEndpoint) (c : ℕ → Bool) (hpq : p.1≠q.1)
    (hrp : r≠p) (hrq : r≠q) :
    bit (restore q.1 (forced p q c) c) r=bit c (spliceEndpoint p q r) := by
  by_cases hr : r.1=q.1
  · have hmate : r=(q.1,!q.2) := by
      apply Prod.ext
      · exact hr
      · rcases r with ⟨e,a⟩
        rcases q with ⟨f,b⟩
        dsimp at hr ⊢
        subst e
        cases a <;> cases b <;> simp_all
    rw [hmate,bit_mate]
    change (Bool.not (bit (restore q.1 (forced p q c) c) q)) = _
    rw [bit_forced]
    simp [spliceEndpoint,removeLoopEndpoint]
  · rw [bit_restore _ _ _ _ hr]
    simp [spliceEndpoint,hr,removeLoopEndpoint]

variable {K : Type*} [CommSemiring K]

 theorem native_selector (p q : RawEndpoint) (c : ℕ → Bool) (d : Bool) (hne : p.1≠q.1) :
    Signature.disequality (K:=K) (bit (restore q.1 d c) p) (bit (restore q.1 d c) q) =
      if d=forced p q c then 1 else 0 := by
  rw [bit_restore _ _ _ _ hne]
  cases hp : p.2 <;> cases hq : q.2 <;> cases hc : c (lowerEdge q.1 p.1) <;> cases d <;>
    simp [bit,restore,forced,removeLoopEndpoint,hp,hq,hc,Signature.disequality]

end Holant.Complexity.UniversalPairReduction.Surgery.Choice
