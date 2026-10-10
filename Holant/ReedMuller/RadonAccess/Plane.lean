import Holant.ReedMuller.RadonAccess.Quotient

/-! Explicit coordinates on the nondegenerate two-plane and the direct-sum
splitting of the translation hyperplane, including the span-quotient relation. -/
namespace Holant.ReedMuller.RadonAccess
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
namespace RadonFrame

theorem v_eq_of_map (F : RadonFrame n) (v : BinaryVector n)
    (h : F.A v = unitWord F.i + unitWord F.j) : F.v = v := by
  apply F.A.linear.injective
  rw [F.map_v,h]

theorem plane_nondegenerate (F : RadonFrame n) (p : F.plane)
    (h : ∀ q : F.plane, dot (p : BinaryVector n) q = 0) : (p : BinaryVector n) = 0 := by
  apply F.plane_inter_complement p.property
  apply (F.complement_iff_orthogonal_plane p).mpr
  intro q hq
  rw [dot_comm]
  exact h ⟨q,hq⟩

/-- The displayed span is a two-plane with explicit independent coordinates. -/
def planeLinearEquiv (F : RadonFrame n) : F.plane ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) where
  toFun p := (dot F.v p, dot F.r p + dot F.v p)
  invFun ab := ⟨ab.1 • F.r + ab.2 • F.v, (F.mem_plane _).mpr ⟨_,_,rfl⟩⟩
  left_inv := by
    intro p
    apply Subtype.ext
    obtain ⟨a,b,hp⟩ := (F.mem_plane p).mp p.property
    change dot F.v p • F.r + (dot F.r p+dot F.v p) • F.v = p
    rw [←hp]
    simp only [dot_add_right,dot_smul_right,F.dot_vr,F.dot_vv,F.dot_rr,F.dot_rv,
      mul_one,mul_zero,add_zero]
    have hh : a+b+a=b := by abel_nf; simp
    rw [hh]
  right_inv := by
    rintro ⟨a,b⟩
    apply Prod.ext
    · simp [dot_add_right,dot_smul_right]
    · simp only [dot_add_right,dot_smul_right,F.dot_vr,F.dot_vv,F.dot_rr,F.dot_rv,
        mul_one,mul_zero,add_zero]
      abel_nf
      simp
  map_add' := by
    intro p q
    apply Prod.ext
    · exact dot_add_right F.v p q
    · change dot F.r (p+q)+dot F.v (p+q)=_
      rw [dot_add_right,dot_add_right]
      change _ = (dot F.r p+dot F.v p)+(dot F.r q+dot F.v q)
      abel
  map_smul' := by
    intro c p
    apply Prod.ext
    · exact dot_smul_right c F.v p
    · change dot F.r (c • (p : BinaryVector n))+dot F.v (c • (p : BinaryVector n)) =
        c*(dot F.r p+dot F.v p)
      rw [dot_smul_right,dot_smul_right,mul_add]

/-- The full translation hyperplane splits as `span(v) ⊕ W`, with its scalar
and complementary summand uniquely recorded in original coordinates. -/
theorem perp_unique_decomposition (F : RadonFrame n) (x : BinaryVector n)
    (hx : dot x F.v = 0) :
    ∃! aw : ZMod 2 × F.complement, x = aw.1 • F.v + aw.2 := by
  have hv : dot F.v x = 0 := by rw [dot_comm]; exact hx
  have hp : F.planePart x = dot F.r x • F.v := by simp [planePart,hv]
  refine ⟨(dot F.r x,⟨F.complementPart x,F.complementPart_mem x⟩),?_,?_⟩
  · simpa only [hp] using F.decomposition x
  · rintro ⟨a,⟨w,hw⟩⟩ h
    have ha : a = dot F.r x := by
      have hh := congrArg (dot F.r) h
      simpa only [dot_add_right,dot_smul_right,F.dot_rv,mul_one,hw.1,add_zero] using hh.symm
    have hw' : w = F.complementPart x := by
      rw [complementPart,hp,←ha,h]
      change w = a • F.v+w+a • F.v
      rw [add_right_comm,binary_add_self,zero_add]
    apply Prod.ext
    · exact ha
    · exact Subtype.ext hw'

/-- The two-point equivalence relation is literally quotienting by the span
of `v`, rather than an unrelated quotient presentation. -/
theorem orbitRel_iff_difference_mem_span (F : RadonFrame n) (ε : ZMod 2)
    (x y : F.Hyperplane ε) :
    F.orbitRel ε x y ↔ x.1+y.1 ∈ Submodule.span (ZMod 2) {F.v} := by
  rw [Submodule.mem_span_singleton]
  constructor
  · intro h
    rcases h with h | h
    · refine ⟨0,?_⟩
      rw [h,binary_add_self,zero_smul]
    · refine ⟨1,?_⟩
      rw [h,one_smul,add_right_comm,binary_add_self,zero_add]
  · rintro ⟨c,hc⟩
    have hb : c = 0 ∨ c = 1 := by
      have hh : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact hh c
    rcases hb with rfl | rfl
    · left
      have hh := congrArg (fun z => z+y.1) hc
      simpa only [zero_smul,zero_add,add_assoc,binary_add_self,add_zero] using hh.symm
    · right
      have hh := congrArg (fun z => z+y.1) hc
      calc
        x.1 = F.v+y.1 := by
          simpa only [one_smul,add_assoc,binary_add_self,add_zero] using hh.symm
        _ = y.1+F.v := add_comm _ _

end RadonFrame
end
end Holant.ReedMuller.RadonAccess
