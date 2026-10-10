import Holant.Certificates.MatchingProductBridge.BridgeRepresentatives
import Holant.Certificates.MatchingProductBridge.TripleAssembly

namespace Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def BridgeVector.Admitted (g : PlatonicModel) : BridgeVector → Prop
  | .regular u _ => groupDirection g (symmetricQuaternion u)
  | _ => True

theorem bridge_admitted_vector (g : PlatonicModel) (W : FourTensor) (h : bridgeConditions g W) :
    ∃ a : BridgeVector, a.Admitted g ∧ W = a.value := by
  rcases (concrete_bridge_real_iff g W).mp h with he | he | he | ⟨u,hu,hg,he⟩
  · exact ⟨.zero,True.intro,he⟩
  · exact ⟨.halfA,True.intro,he⟩
  · exact ⟨.halfB,True.intro,he⟩
  · exact ⟨.regular u hu,hg,he⟩

theorem BridgeVector.admitted_regular (g : PlatonicModel) (a : BridgeVector)
    (ha : a.Admitted g) (hc : a.code = 3) :
    ∃ u : Fin 3 → ℝ, u ≠ 0 ∧ groupDirection g (symmetricQuaternion u) ∧ a.value = R u := by
  cases a with
  | zero => simp [BridgeVector.code] at hc
  | halfA => simp [BridgeVector.code] at hc
  | halfB => simp [BridgeVector.code] at hc
  | regular u hu => exact ⟨u,hu,ha,rfl⟩

/-- The source's complete exceptional-or-orthogonal triple alternative, now for
actual T/O/I bridge vectors and retaining their genuine group-direction membership. -/
theorem concrete_bridge_triple_iff (g : PlatonicModel) (W X Y : FourTensor)
    (hW : bridgeConditions g W) (hX : bridgeConditions g X) (hY : bridgeConditions g Y) :
    W+X+Y = (fun x => (A x+B x)/2) ↔
      List.Perm [W,X,Y] [0,(1/2 : ℂ) • A,(1/2 : ℂ) • B] ∨
      ∃ u v w : Fin 3 → ℝ, u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧
        groupDirection g (symmetricQuaternion u) ∧ groupDirection g (symmetricQuaternion v) ∧
        groupDirection g (symmetricQuaternion w) ∧ W = R u ∧ X = R v ∧ Y = R w ∧
        dot u v = 0 ∧ dot u w = 0 ∧ dot v w = 0 := by
  rcases bridge_admitted_vector g W hW with ⟨a,ha,rfl⟩
  rcases bridge_admitted_vector g X hX with ⟨b,hb,rfl⟩
  rcases bridge_admitted_vector g Y hY with ⟨c,hc,rfl⟩
  constructor
  · intro h
    rcases a.sum_code_patterns b c h with he | ⟨ha3,hb3,hc3⟩
    · exact Or.inl (a.exceptional_perm b c he)
    · rcases a.admitted_regular g ha ha3 with ⟨u,hu,hgu,hau⟩
      rcases b.admitted_regular g hb hb3 with ⟨v,hv,hgv,hbv⟩
      rcases c.admitted_regular g hc hc3 with ⟨w,hw,hgw,hcw⟩
      rw [hau,hbv,hcw] at h
      exact Or.inr ⟨u,v,w,hu,hv,hw,hgu,hgv,hgw,hau,hbv,hcw,
        (R_triple_sum_iff_orthogonal u v w hu hv hw).mp h⟩
  · rintro (he | ⟨u,v,w,hu,hv,hw,_,_,_,hau,hbv,hcw,ho⟩)
    · have hh := he.sum_eq
      simpa only [List.sum_cons,List.sum_nil,add_zero,zero_add,add_assoc] using
        hh.trans (by simpa only [List.sum_cons,List.sum_nil,add_zero,zero_add,add_assoc] using exceptional_triple_sum)
    · rw [hau,hbv,hcw]
      exact (R_triple_sum_iff_orthogonal u v w hu hv hw).mpr ho

end
end Holant.Certificates.MatchingProductBridge
