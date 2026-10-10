import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Fixed finite residue witnesses for tensor-power removal. An unattainable
nonzero residue is answered by zero. An attainable residue has one fixed
nonzero padding witness; no runtime search or witness premise is introduced.
The physical disjoint-union/grouping compiler consumes these facts separately. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalWitness
open Classical
set_option backward.isDefEq.respectTransparency false
variable {I K : Type*} [Field K]
variable (occurrences : I → ℕ) (value : I → K) (k : ℕ)

def Active (r : Fin k) : Prop := ∃J, occurrences J % k=r.val ∧ value J≠0

def chosen (r : Fin k) (h : Active occurrences value k r) : I := Classical.choose h

theorem chosen_spec (r : Fin k) (h : Active occurrences value k r) :
    occurrences (chosen occurrences value k r h) % k=r.val ∧
      value (chosen occurrences value k r h)≠0 := Classical.choose_spec h

def witness (r : Fin k) : Option I :=
  if h : Active occurrences value k r then some (chosen occurrences value k r h) else none

theorem witness_none (r : Fin k) : witness occurrences value k r=none ↔
    ∀J,occurrences J % k=r.val → value J=0 := by
  unfold witness
  split_ifs with h
  · simp only [false_iff]
    obtain ⟨J,hJ,hv⟩ := h
    intro hz
    exact hv (hz J hJ)
  · simp only [true_iff]
    intro J hJ
    by_contra hv
    exact h ⟨J,hJ,hv⟩

theorem witness_some (r : Fin k) (J : I) (hJ : witness occurrences value k r=some J) :
    occurrences J % k=r.val ∧ value J≠0 := by
  unfold witness at hJ
  split_ifs at hJ with h
  · cases Option.some.inj hJ
    exact chosen_spec occurrences value k r h

variable (hk : 0<k)

def residue (J : I) : Fin k := ⟨occurrences J % k,Nat.mod_lt _ hk⟩

theorem input_active (J : I) (hv : value J≠0) :
    Active occurrences value k (residue occurrences k hk J) := ⟨J,rfl,hv⟩

theorem inactive_input_zero (J : I)
    (h : ¬Active occurrences value k (residue occurrences k hk J)) : value J=0 := by
  by_contra hv
  exact h (input_active occurrences value k hk J hv)

def correction (r : Fin k) (h : Active occurrences value k r) : K :=
  value (chosen occurrences value k r h)^(k-1)

theorem correction_ne_zero (r : Fin k) (h : Active occurrences value k r) :
    correction occurrences value k r h≠0 :=
  pow_ne_zero _ (chosen_spec occurrences value k r h).2

include hk in
theorem padded_count_mod (J W : I) (h : occurrences J % k=occurrences W % k) :
    (occurrences J+(k-1)*occurrences W)%k=0 := by
  have he : occurrences W+(k-1)*occurrences W=k*occurrences W := by
    have hk' : k-1+1=k := by omega
    calc
      _ = ((k-1)+1)*occurrences W := by ring
      _ = _ := by rw [hk']
  calc
    _ = (occurrences W+(k-1)*occurrences W)%k := by
      calc
        _ = (occurrences J%k+((k-1)*occurrences W)%k)%k := Nat.add_mod _ _ _
        _ = (occurrences W%k+((k-1)*occurrences W)%k)%k := by rw [h]
        _ = _ := (Nat.add_mod _ _ _).symm
    _ = 0 := by rw [he]; simp

include hk in
theorem padded_count_dvd (J : I) (r : Fin k) (hJ : occurrences J % k=r.val)
    (h : Active occurrences value k r) :
    k ∣ occurrences J+(k-1)*occurrences (chosen occurrences value k r h) :=
  Nat.dvd_of_mod_eq_zero (padded_count_mod occurrences k hk J _
    (hJ.trans (chosen_spec occurrences value k r h).1.symm))

theorem normalized_value (J : I) (r : Fin k) (h : Active occurrences value k r) :
    (value J * correction occurrences value k r h) / correction occurrences value k r h=value J :=
  mul_div_cancel_right₀ _ (correction_ne_zero occurrences value k r h)

/-- Every chosen witness has a fixed finite size bound, for any supplied
structural size measure. This does not assert a bound for finding a witness. -/
def sizeBound (size : I → ℕ) : ℕ :=
  Finset.univ.sup (fun r : Fin k => if h : Active occurrences value k r then
    size (chosen occurrences value k r h) else 0)

theorem chosen_size_le (size : I → ℕ) (r : Fin k) (h : Active occurrences value k r) :
    size (chosen occurrences value k r h) ≤ sizeBound occurrences value k size := by
  have hp := Finset.le_sup (f:=fun r : Fin k => if h : Active occurrences value k r then
    size (chosen occurrences value k r h) else 0) (Finset.mem_univ r)
  simpa only [sizeBound,dite_eq_left h] using hp

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalWitness
