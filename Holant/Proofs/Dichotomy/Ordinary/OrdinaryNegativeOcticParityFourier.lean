import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeOcticParityIdentity
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentOrdinarySquare

/-! A positive Fourier block for the seven-parity cubic identity. The literal
row list uses only H, T and pin0. All old logical ports and every private
variable have even incidence; no parity signature or free summation unary
is introduced as a row label. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticParityFourier
open Holant Holant.Tractable
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open scoped BigOperators
namespace I
export OrdinaryNegativeOcticParityIdentity (mask parity terms value term_count cubic_identity)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

variable {K : Type*} [CommRing K]
def character (u b : Bool) : K := if u && b then -1 else 1

theorem character_xor (u b c : Bool) :
    character (K:=K) u (Bool.xor b c)=character u b*character u c := by
  cases u <;> cases b <;> cases c <;> simp [character]

theorem character_and (u b c : Bool) :
    character (K:=K) u (b && c)=if b then character u c else 1 := by
  cases b <;> simp [character]

def inputProduct (m : Fin 8) (u : Bool) (x : Fin 3 → Bool) : K :=
  ∏j,if I.mask m j then character u (x j) else 1

theorem inputProduct_eq (m : Fin 8) (u : Bool) (x : Fin 3 → Bool) :
    inputProduct (K:=K) m u x=character u (I.parity m x) := by
  simp only [inputProduct,Fin.prod_univ_three,OrdinaryNegativeOcticParityIdentity.parity,
    character_xor,character_and]

/-- The actual two private bits of one phase block are summed. -/
def termWeight (z : K) (m : Fin 8) (x : Fin 3 → Bool) (u t : Bool) : K :=
  z^t.toNat*character u t*inputProduct m u x

theorem term_fourier (z : K) (m : Fin 8) (x : Fin 3 → Bool) :
    (∑u : Bool,∑t : Bool,termWeight z m x u t)=2*z^(I.parity m x).toNat := by
  simp only [termWeight,inputProduct_eq]
  cases I.parity m x <;> simp [character] <;> ring

/-- Pair masks need one H(u,0) to make the center degree even; it is a
literal H row sharing the single pinned-zero variable of the whole block. -/
def pairMask (m : Fin 8) : Bool := m=3 || m=5 || m=6

def term (v : Fin 25) : Fin 8 := I.terms.get ⟨v.val,by rw [I.term_count]; exact v.isLt⟩
def center (v : Fin 25) : ℕ := 3+2*v.val
def phase (v : Fin 25) : ℕ := 3+2*v.val+1
def constant : ℕ := 53

def termRows (v : Fin 25) : List Factor :=
  [(1,[phase v]),(0,[center v,phase v])] ++
    ((List.finRange 3).filter (fun j=>I.mask (term v) j)).map (fun j=>(0,[center v,j.val])) ++
    (if pairMask (term v) then [(0,[center v,constant])] else [])

def factors : List Factor := (List.finRange 25).flatMap termRows ++ [(2,[constant])]
def raw : Raw := ⟨54,factors⟩
def arity (i : ℕ) : ℕ := if i=0 then 2 else 1

theorem logical_count (i : Fin 3) : (factors.flatMap Prod.snd).count i.val=16 := by
  fin_cases i <;> decide

theorem phase_count (v : Fin 25) : (factors.flatMap Prod.snd).count (phase v)=2 := by
  fin_cases v <;> decide

theorem center_even (v : Fin 25) : Even ((factors.flatMap Prod.snd).count (center v)) := by
  fin_cases v <;> decide

theorem constant_count : (factors.flatMap Prod.snd).count constant=22 := by decide

theorem all_addresses_valid : ∀r∈factors,r.1<3 ∧ r.2.length=arity r.1 ∧ ∀i∈r.2,i<54 := by
  decide

theorem even_counts : ∀i : Fin 54,Even ((factors.flatMap Prod.snd).count i.val) := by
  decide

theorem raw_valid : raw.Valid 3 arity := by
  refine ⟨?_,?_,?_⟩
  · intro v
    have h := all_addresses_valid (raw.factors.get v) (List.get_mem _ _)
    exact ⟨h.1,h.2.1⟩
  · intro p
    exact (all_addresses_valid (raw.factors.get p.1) (List.get_mem _ _)).2.2 _ (List.get_mem _ _)
  · intro i hi
    rw [StableHigherCurrentOrdinarySquare.degree_flat]
    exact even_counts ⟨i,hi⟩

def blockWeight (z : K) (x : Fin 3 → Bool) (bits : Fin 25 → Bool×Bool) : K :=
  ∏v,termWeight z (term v) x (bits v).1 (bits v).2

theorem block_fourier (z : K) (x : Fin 3 → Bool) :
    (∑bits : Fin 25 → Bool×Bool,blockWeight z x bits)=2^25*I.value z x := by
  unfold blockWeight
  rw [←Fintype.prod_sum (fun (v : Fin 25) (y : Bool×Bool)=>termWeight z (term v) x y.1 y.2)]
  simp_rw [Fintype.sum_prod_type,term_fourier]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  congr 1

theorem block_cubic (z : K) (hfour : z^4= -1) (x : Fin 3 → Bool) :
    (∑bits : Fin 25 → Bool×Bool,blockWeight z x bits)=
      2^25*OrdinaryNegativeCubicCore.cubic x := by
  rw [block_fourier,I.cubic_identity z hfour]
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticParityFourier
end
