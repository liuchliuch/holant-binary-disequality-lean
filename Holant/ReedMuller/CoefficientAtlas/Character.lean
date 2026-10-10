import Holant.ReedMuller.CoefficientAtlas.Algebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

namespace Holant.ReedMuller.CoefficientAtlas
open Holant.ReedMuller.LowArity
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

variable {G : Type*} [CommGroup G]

def sign (u : G) (a : ZMod 2) : G := if a=0 then 1 else u

def boolValue (b : Bool) : ZMod 2 := if b then 1 else 0

theorem sign_add (u : G) (hu : u*u=1) (a b : ZMod 2) :
    sign u (a+b)=sign u a*sign u b := by
  fin_cases a <;> fin_cases b
  · change 1=(1:G)*1
    simp
  · change u=1*u
    simp
  · change u=u*1
    simp
  · change 1=u*u
    exact hu.symm

theorem sign_sum {ι : Type*} (u : G) (hu : u*u=1) (S : Finset ι) (f : ι → ZMod 2) :
    sign u (∑ i ∈ S, f i)=∏ i ∈ S, sign u (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sign]
  | @insert i S hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,sign_add u hu,ih]

def basis (i : Fin 4) : Param := Pi.single i 1

theorem basis_expansion : ∀ a : Param, a=∑ i, a i • basis i := by decide

theorem map_sum (w : Param → G) (h0 : w 0=1)
    (hm : ∀ a b, w (a+b)=w a*w b) {ι : Type*} (S : Finset ι) (f : ι → Param) :
    w (∑ i ∈ S, f i)=∏ i ∈ S, w (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [h0]
  | @insert i S hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,hm,ih]

theorem coefficient_formula {w : Param → G} (h0 : w 0=1) (h : CubeProducts w) (a : Param) :
    w a=∏ i, w (basis i)^(a i).val := by
  conv_lhs => rw [basis_expansion a]
  rw [map_sum w h0 (multiplicative h0 h)]
  apply Finset.prod_congr rfl
  intro i _
  have hz : ∀ z : ZMod 2, w (z • basis i)=w (basis i)^z.val := by
    intro z
    fin_cases z <;> norm_num [h0,ZMod.val_natCast,ZMod.val_one_eq_one_mod,ZMod.natCast_self]
  exact hz (a i)

theorem sign_mul (u : G) (hu : u*u=1) (b a : ZMod 2) :
    sign u (b*a)=(sign u b)^a.val := by
  fin_cases b <;> fin_cases a <;> norm_num [sign,hu,ZMod.val_natCast,ZMod.val_one_eq_one_mod,ZMod.natCast_self]

theorem unit_sign (u : ℂˣ) (hu : u*u=1) :
    ∃ b : Bool, u=sign (-1 : ℂˣ) (boolValue b) := by
  have hc : (u:ℂ)^2=1 := by
    simpa only [Units.val_mul,Units.val_one,pow_two] using congrArg (fun v : ℂˣ => (v:ℂ)) hu
  rcases sq_eq_one_iff.mp hc with h1 | hm
  · refine ⟨false,?_⟩
    apply Units.ext
    simpa [sign,boolValue] using h1
  · refine ⟨true,?_⟩
    apply Units.ext
    simpa [sign,boolValue] using hm

/-- Every normalized coefficient is an actual sign character of the four
independent affine-evaluation parameters. -/
theorem parameter_character {w : Param → ℂˣ} (h0 : w 0=1) (h : CubeProducts w) :
    ∃ b : Fin 4 → Bool, ∀ a : Param,
      w a=sign (-1 : ℂˣ) (∑ i, boolValue (b i)*a i) := by
  choose b hb using fun i : Fin 4 => unit_sign (w (basis i)) (square h0 h (basis i))
  refine ⟨b,?_⟩
  intro a
  rw [coefficient_formula h0 h a,sign_sum _ (by simp)]
  apply Finset.prod_congr rfl
  intro i _
  rw [hb i,sign_mul _ (by simp)]

/-- A concrete extension of the character to the original eight coordinates. -/
def ambient (b : Fin 4 → Bool) : BinaryVector 8 :=
  ![boolValue (b 0)+boolValue (b 1)+boolValue (b 2)+boolValue (b 3),
    boolValue (b 1),boolValue (b 2),0,boolValue (b 3),0,0,0]

theorem ambient_dot : ∀ b : Fin 4 → Bool, ∀ a : Param,
    dot (ambient b) (evaluate a)=∑ i, boolValue (b i)*a i := by decide

theorem ambient_character {w : Param → ℂˣ} (h0 : w 0=1) (h : CubeProducts w) :
    ∃ v : BinaryVector 8, ∀ a : Param, w a=sign (-1 : ℂˣ) (dot v (evaluate a)) := by
  obtain ⟨b,hb⟩ := parameter_character h0 h
  exact ⟨ambient b,fun a => by rw [ambient_dot]; exact hb a⟩

end Holant.ReedMuller.CoefficientAtlas
