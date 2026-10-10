import Holant.Tractable.Criteria
import Mathlib.Tactic

/-! Generic origin-supported Product geometry, independent of extraction
programmes and any physical availability claim. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionSupport
open Holant Holant.Tractable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {n : ℕ}

def origin : Fin n → Bool := fun _ => false
def xor (u v : Fin n → Bool) : Fin n → Bool := fun i => Bool.xor (u i) (v i)
def meet (u v : Fin n → Bool) : Fin n → Bool := fun i => u i && v i


def XorClosed (f : Signature AlgebraicComplex n) : Prop :=
  ∀u v,f u≠0 → f v≠0 → f (xor u v)≠0

def MeetClosed (f : Signature AlgebraicComplex n) : Prop :=
  ∀u v,f u≠0 → f v≠0 → f (meet u v)≠0


private theorem factor_meet (p : ProductFactor n) (u v : Fin n → Bool)
    (h0 : p.eval origin≠0) (hu : p.eval u≠0) (hv : p.eval v≠0) : p.eval (meet u v)≠0 := by
  cases p with
  | unary i a ha =>
    cases hi : u i with
    | false => simpa [ProductFactor.eval,meet,origin,hi] using h0
    | true => simpa [ProductFactor.eval,meet,hi] using hv
  | equality i j =>
    have hi : u i=u j := by simpa [ProductFactor.eval,Signature.equality] using hu
    have hj : v i=v j := by simpa [ProductFactor.eval,Signature.equality] using hv
    simp [ProductFactor.eval,Signature.equality,meet,hi,hj]
  | disequality i j =>
    simp [ProductFactor.eval,Signature.disequality,origin] at h0

/-- At an origin-supported Product row, every literal equality/disequality
factor and unary weight force support closure under intersection. -/
theorem product_meetClosed (f : Signature AlgebraicComplex n) (h0 : f origin≠0)
    (hp : Product f) : MeetClosed f := by
  rcases hp with hz | ⟨c,hc,ps,rfl⟩
  · exact False.elim (h0 (congrFun hz origin))
  intro u v hu hv
  have factor (x : Fin n → Bool) (hx : productFormula c ps x≠0)
      (p : ProductFactor n) (hp : p∈ps) : p.eval x≠0 := by
    intro hz
    apply hx
    have hzprod : (ps.map (fun p => p.eval x)).prod=0 :=
      List.prod_eq_zero (List.mem_map.mpr ⟨p,hp,hz⟩)
    simp only [productFormula,hzprod,mul_zero]
  change c*(ps.map (fun p => p.eval (meet u v))).prod≠0
  apply mul_ne_zero hc
  apply List.prod_ne_zero
  intro hz
  obtain ⟨p,hp,hz⟩ := List.mem_map.mp hz
  exact factor_meet p u v (factor origin h0 p hp) (factor u hu p hp) (factor v hv p hp) hz

/-- Group source coordinates by the actual pair of support bits. No signed
literal occurs: each old coordinate is false, z0, z1 or z2. -/
def parityWord (u v : Fin n → Bool) (z : Fin 3 → Bool) : Fin n → Bool := fun i =>
  if u i then (if v i then z 2 else z 0) else (if v i then z 1 else false)

def parityRow (f : Signature AlgebraicComplex n) (u v : Fin n → Bool) :
    Signature AlgebraicComplex 3 := fun z => f (parityWord u v z)

private theorem word000 (u v : Fin n → Bool) : parityWord u v ![false,false,false]=origin := by
  funext i; cases hu : u i <;> cases hv : v i <;> simp [parityWord,origin,hu,hv]
private theorem word101 (u v : Fin n → Bool) : parityWord u v ![true,false,true]=u := by
  funext i; cases hu : u i <;> cases hv : v i <;> simp [parityWord,hu,hv]
private theorem word011 (u v : Fin n → Bool) : parityWord u v ![false,true,true]=v := by
  funext i; cases hu : u i <;> cases hv : v i <;> simp [parityWord,hu,hv]
private theorem word110 (u v : Fin n → Bool) : parityWord u v ![true,true,false]=xor u v := by
  funext i; cases hu : u i <;> cases hv : v i <;> simp [parityWord,xor,hu,hv]
private theorem word001 (u v : Fin n → Bool) : parityWord u v ![false,false,true]=meet u v := by
  funext i; cases hu : u i <;> cases hv : v i <;> simp [parityWord,meet,hu,hv]
private theorem word100 (u v : Fin n → Bool) : xor u (parityWord u v ![true,false,false])=meet u v := by
  funext i; cases hu : u i <;> cases hv : v i <;> simp [parityWord,xor,meet,hu,hv]
private theorem word010 (u v : Fin n → Bool) : xor v (parityWord u v ![false,true,false])=meet u v := by
  funext i; cases hu : u i <;> cases hv : v i <;> simp [parityWord,xor,meet,hu,hv]
private theorem word111 (u v : Fin n → Bool) : xor (xor u v) (parityWord u v ![true,true,true])=meet u v := by
  funext i; cases hu : u i <;> cases hv : v i <;> simp [parityWord,xor,meet,hu,hv]

theorem parity_support (f : Signature AlgebraicComplex n) (h0 : f origin≠0)
    (hx : XorClosed f) (u v : Fin n → Bool) (hu : f u≠0) (hv : f v≠0)
    (hm : f (meet u v)=0) (z : Fin 3 → Bool) :
    parityRow f u v z≠0 ↔ Bool.xor (Bool.xor (z 0) (z 1)) (z 2)=false := by
  have h01 := hx u v hu hv
  have h100 : f (parityWord u v ![true,false,false])=0 := by
    by_contra hh
    have hn := hx u _ hu hh
    rw [word100,hm] at hn
    exact hn rfl
  have h010 : f (parityWord u v ![false,true,false])=0 := by
    by_contra hh
    have hn := hx v _ hv hh
    rw [word010,hm] at hn
    exact hn rfl
  have h111 : f (parityWord u v ![true,true,true])=0 := by
    by_contra hh
    have hn := hx (xor u v) _ h01 hh
    rw [word111,hm] at hn
    exact hn rfl
  have hz : z=![z 0,z 1,z 2] := by funext i; fin_cases i <;> rfl
  rw [hz]
  cases z 0 <;> cases z 1 <;> cases z 2 <;>
    simp [parityRow,word000,word001,word101,word011,word110,h100,h010,h111,h0,hu,hv,hm,h01]

theorem parity_not_product (f : Signature AlgebraicComplex n) (h0 : f origin≠0)
    (u v : Fin n → Bool) (hu : f u≠0) (hv : f v≠0)
    (hm : f (meet u v)=0) : ¬Product (parityRow f u v) := by
  intro hp
  have hzero : parityRow f u v origin≠0 := by
    simpa only [parityRow, show (origin : Fin 3 → Bool)=![false,false,false] from by funext i; fin_cases i <;> rfl, word000] using h0
  have hmeet := product_meetClosed (parityRow f u v) hzero hp
    ![true,false,true] ![false,true,true]
    (by simpa only [parityRow,word101] using hu)
    (by simpa only [parityRow,word011] using hv)
  have he : meet (![true,false,true] : Fin 3 → Bool) ![false,true,true]=![false,false,true] := by
    funext i; fin_cases i <;> rfl
  simp only [he,parityRow,word001,hm,ne_eq,not_true_eq_false] at hmeet

/-- Negating a generic support closure property internally extracts the two
support words and the ternary parity minor. It is not a supplied parity row. -/
theorem exists_parity (f : Signature AlgebraicComplex n) (h0 : f origin≠0)
    (hx : XorClosed f) (hm : ¬MeetClosed f) :
    ∃u v : Fin n → Bool,f u≠0 ∧ f v≠0 ∧
      (∀z,parityRow f u v z≠0 ↔ Bool.xor (Bool.xor (z 0) (z 1)) (z 2)=false) ∧
      ¬Product (parityRow f u v) := by
  unfold MeetClosed at hm
  push Not at hm
  obtain ⟨u,v,hu,hv,hm⟩ := hm
  exact ⟨u,v,hu,hv,parity_support f h0 hx u v hu hv hm,parity_not_product f h0 u v hu hv hm⟩


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionSupport
end
