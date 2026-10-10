import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicCore
import Holant.Tractable.Scalars
import Mathlib.Data.List.Count

/-! Literal positive-power seven-parity synthesis of a cubic sign. This is
an algebraic identity and an exact incidence count; parity gates still require
physical synthesis by the caller and are not declared free signatures. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticParityIdentity
open Holant Holant.Tractable
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

def mask : Fin 8 → Fin 3 → Bool :=
  ![![false,false,false],![true,false,false],![false,true,false],![true,true,false],
    ![false,false,true],![true,false,true],![false,true,true],![true,true,true]]

def parity (m : Fin 8) (x : Fin 3 → Bool) : Bool :=
  Bool.xor (Bool.xor (mask m 0 && x 0) (mask m 1 && x 1)) (mask m 2 && x 2)

/-- Three positive unary phases, seven copies of each inverse pair phase,
and one positive triple phase. All 25 factors are positive copies. -/
def terms : List (Fin 8) :=
  [1,2,4] ++ List.replicate 7 3 ++ List.replicate 7 5 ++ List.replicate 7 6 ++ [7]

def exponent (x : Fin 3 → Bool) : ℕ := (terms.map (fun m=>(parity m x).toNat)).sum

variable {K : Type*} [CommRing K]
def value (z : K) (x : Fin 3 → Bool) : K :=
  (terms.map (fun m=>z^((parity m x).toNat))).prod

theorem value_eq_pow (z : K) (x : Fin 3 → Bool) : value z x=z^(exponent x) := by
  unfold value exponent
  induction terms with
  | nil => simp
  | cons m ms ih => simp only [List.map_cons,List.prod_cons,List.sum_cons,pow_add,ih]

theorem exponent_exact (x : Fin 3 → Bool) : exponent x=
    if x 0 && x 1 && x 2 then 4 else if x 0 || x 1 || x 2 then 16 else 0 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    norm_num [exponent,terms,parity,mask,h0,h1,h2]

theorem eighth_power (z : K) (hfour : z^4= -1) : z^8=1 := by
  calc z^8=(z^4)^2 := by ring
       _=1 := by rw [hfour]; ring

/-- The literal finite product, rather than a formal phase-polynomial oracle. -/
theorem cubic_identity (z : K) (hfour : z^4= -1) (x : Fin 3 → Bool) :
    value z x=OrdinaryNegativeCubicCore.cubic x := by
  rw [value_eq_pow,exponent_exact]
  have h16 : z^16=1 := by
    calc z^16=(z^8)^2 := by ring
         _=1 := by rw [eighth_power z hfour]; simp
  unfold OrdinaryNegativeCubicCore.cubic
  split_ifs <;> simp_all

/-- Every logical input occurs sixteen times, including the seven positive
copies implementing each inverse. This counts the actual factor list. -/
theorem occurrences (i : Fin 3) : (terms.filter (fun m=>mask m i)).length=16 := by
  fin_cases i <;> decide

theorem term_count : terms.length=25 := by decide

theorem even_occurrences (i : Fin 3) : Even ((terms.filter (fun m=>mask m i)).length) := by
  rw [occurrences]
  decide

theorem zetaEight_identity (x : Fin 3 → Bool) :
    value zetaEight x=OrdinaryNegativeCubicCore.cubic x :=
  cubic_identity zetaEight zetaEight_pow_four x
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticParityIdentity
end
