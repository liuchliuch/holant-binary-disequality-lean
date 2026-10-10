import Holant.Certificates.MatchingProductBridge.TripleFunctionals
import Mathlib.Data.List.Perm.Basic

/-! Complete sum classification for the source's proposed bridge-vector family.
The separate claim that this family exhausts each Platonic matching cone is not
assumed here and remains a distinct obligation. -/
namespace Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive BridgeVector where
  | zero
  | halfA
  | halfB
  | regular (u : Fin 3 → ℝ) (nonzero : u ≠ 0)

def BridgeVector.value : BridgeVector → FourTensor
  | .zero => 0
  | .halfA => (1/2 : ℂ) • A
  | .halfB => (1/2 : ℂ) • B
  | .regular u _ => R u

def BridgeVector.code : BridgeVector → Fin 4
  | .zero => 0
  | .halfA => 1
  | .halfB => 2
  | .regular _ _ => 3

def antiCode : Fin 4 → ℤ := ![0,1,-1,0]
def traceCode : Fin 4 → ℤ := ![0,3,3,2]

theorem BridgeVector.anti_weight (v : BridgeVector) :
    (antiCode v.code : ℂ) = 4*antisymmetricCoefficient v.value := by
  cases v with
  | zero => norm_num [code,value,antiCode,antisymmetricCoefficient_zero]
  | halfA => norm_num [code,value,antiCode,antisymmetricCoefficient_half_A]
  | halfB => norm_num [code,value,antiCode,antisymmetricCoefficient_half_B]
  | regular u hu => norm_num [code,value,antiCode,antisymmetricCoefficient_R]

theorem BridgeVector.trace_weight (v : BridgeVector) :
    (traceCode v.code : ℂ) = 2*traceCoefficient v.value := by
  cases v with
  | zero => norm_num [code,value,traceCode,traceCoefficient_zero]
  | halfA => norm_num [code,value,traceCode,traceCoefficient_half_A]
  | halfB => norm_num [code,value,traceCode,traceCoefficient_half_B]
  | regular u hu => norm_num [code,value,traceCode,traceCoefficient_R u hu]

theorem bridge_code_patterns : ∀ a b c : Fin 4,
    antiCode a+antiCode b+antiCode c = 0 → traceCode a+traceCode b+traceCode c = 6 →
    List.Perm [a,b,c] [0,1,2] ∨ a = 3 ∧ b = 3 ∧ c = 3 := by decide

theorem BridgeVector.sum_code_patterns (a b c : BridgeVector)
    (h : a.value+b.value+c.value = (fun x => (A x+B x)/2)) :
    List.Perm [a.code,b.code,c.code] [0,1,2] ∨ a.code = 3 ∧ b.code = 3 ∧ c.code = 3 := by
  have ha := congrArg antisymmetricCoefficient h
  rw [antisymmetricCoefficient_add,antisymmetricCoefficient_add,antisymmetricCoefficient_target] at ha
  have ht := congrArg traceCoefficient h
  rw [traceCoefficient_add,traceCoefficient_add,traceCoefficient_target] at ht
  apply bridge_code_patterns
  · have hh : ((antiCode a.code+antiCode b.code+antiCode c.code : ℤ) : ℂ) = 0 := by
      push_cast
      rw [a.anti_weight,b.anti_weight,c.anti_weight]
      linear_combination 4*ha
    exact_mod_cast hh
  · have hh : ((traceCode a.code+traceCode b.code+traceCode c.code : ℤ) : ℂ) = 6 := by
      push_cast
      rw [a.trace_weight,b.trace_weight,c.trace_weight]
      linear_combination 2*ht
    exact_mod_cast hh

def exceptionalValue : Fin 4 → FourTensor := ![0,(1/2 : ℂ) • A,(1/2 : ℂ) • B,0]

theorem BridgeVector.value_of_nonregular (v : BridgeVector) (h : v.code ≠ 3) :
    v.value = exceptionalValue v.code := by
  cases v with
  | zero => rfl
  | halfA => rfl
  | halfB => rfl
  | regular u hu => exact (h rfl).elim

theorem BridgeVector.regular_of_code (v : BridgeVector) (h : v.code = 3) :
    ∃ u : Fin 3 → ℝ, u ≠ 0 ∧ v.value = R u := by
  cases v with
  | zero => simp [code] at h
  | halfA => simp [code] at h
  | halfB => simp [code] at h
  | regular u hu => exact ⟨u,hu,rfl⟩

theorem BridgeVector.exceptional_perm (a b c : BridgeVector)
    (h : List.Perm [a.code,b.code,c.code] [0,1,2]) :
    List.Perm [a.value,b.value,c.value] [0,(1/2 : ℂ) • A,(1/2 : ℂ) • B] := by
  have ha : a.code ≠ 3 := by
    intro he
    have hh := h.mem_iff.mp (by simp : a.code ∈ [a.code,b.code,c.code])
    simp [he] at hh
  have hb : b.code ≠ 3 := by
    intro he
    have hh := h.mem_iff.mp (by simp : b.code ∈ [a.code,b.code,c.code])
    simp [he] at hh
  have hc : c.code ≠ 3 := by
    intro he
    have hh := h.mem_iff.mp (by simp : c.code ∈ [a.code,b.code,c.code])
    simp [he] at hh
  have hm := h.map exceptionalValue
  simp only [List.map_cons,List.map_nil] at hm
  rw [← a.value_of_nonregular ha,← b.value_of_nonregular hb,← c.value_of_nonregular hc] at hm
  change List.Perm [a.value,b.value,c.value] [0,(1/2 : ℂ) • A,(1/2 : ℂ) • B] at hm
  exact hm

/-- Exact exceptional-or-orthogonal classification of triples of proposed bridge vectors. -/
theorem BridgeVector.triple_sum_iff (a b c : BridgeVector) :
    a.value+b.value+c.value = (fun x => (A x+B x)/2) ↔
      List.Perm [a.value,b.value,c.value] [0,(1/2 : ℂ) • A,(1/2 : ℂ) • B] ∨
      ∃ u v w : Fin 3 → ℝ, u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧
        a.value = R u ∧ b.value = R v ∧ c.value = R w ∧
        dot u v = 0 ∧ dot u w = 0 ∧ dot v w = 0 := by
  constructor
  · intro h
    rcases a.sum_code_patterns b c h with he | ⟨ha,hb,hc⟩
    · exact Or.inl (a.exceptional_perm b c he)
    · rcases a.regular_of_code ha with ⟨u,hu,hau⟩
      rcases b.regular_of_code hb with ⟨v,hv,hbv⟩
      rcases c.regular_of_code hc with ⟨w,hw,hcw⟩
      rw [hau,hbv,hcw] at h
      exact Or.inr ⟨u,v,w,hu,hv,hw,hau,hbv,hcw,(R_triple_sum_iff_orthogonal u v w hu hv hw).mp h⟩
  · rintro (h | ⟨u,v,w,hu,hv,hw,hau,hbv,hcw,ho⟩)
    · have he := h.sum_eq
      have ht := exceptional_triple_sum
      simpa only [List.sum_cons,List.sum_nil,add_zero,zero_add,add_assoc] using
        he.trans (by simpa only [List.sum_cons,List.sum_nil,add_zero,zero_add,add_assoc] using ht)
    · rw [hau,hbv,hcw]
      exact (R_triple_sum_iff_orthogonal u v w hu hv hw).mpr ho

end
end Holant.Certificates.MatchingProductBridge
