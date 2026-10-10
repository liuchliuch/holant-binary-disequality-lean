import Holant.ReedMuller.LowArity.HalfDimension

/-! Actual independent accessible directions inside any sufficiently large
even binary subspace, excluding the zero/all-one exceptions explicitly. -/
namespace Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

 theorem exists_accessible_triple (W : BinaryCode n)
    (heven : ∀ x,x∈W → dot (ones n) x=0)
    (hdim : 3≤Module.finrank (ZMod 2) W) :
    ∃ p q : BinaryVector n,p∈W ∧ q∈W ∧ Accessible p ∧ Accessible q ∧ Accessible (p+q) := by
  have hline : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({ones n}:Set (BinaryVector n)))≤1 := by
    simpa using (finrank_span_le_card ({ones n}:Set (BinaryVector n)))
  have hn : ¬W≤Submodule.span (ZMod 2) ({ones n}:Set (BinaryVector n)) := by
    intro h
    have H := (Submodule.finrank_mono h).trans hline
    omega
  change ¬∀ p,p∈W → p∈Submodule.span (ZMod 2) ({ones n}:Set (BinaryVector n)) at hn
  push_neg at hn
  obtain ⟨p,hp,hpn⟩ := hn
  let T := Submodule.span (ZMod 2) ({ones n,p}:Set (BinaryVector n))
  have htwo : Module.finrank (ZMod 2) T≤2 := by
    have H := finrank_span_le_card (R:=ZMod 2) ({ones n,p}:Set (BinaryVector n))
    have hc : ({ones n,p}:Set (BinaryVector n)).toFinset=({ones n,p}:Finset (BinaryVector n)) := by ext x;simp
    rw [hc] at H
    exact H.trans Finset.card_le_two
  have hnq : ¬W≤T := by
    intro h
    have H := (Submodule.finrank_mono h).trans htwo
    omega
  change ¬∀ q,q∈W → q∈T at hnq
  push_neg at hnq
  obtain ⟨q,hq,hqn⟩ := hnq
  have hones : ones n∈T := Submodule.subset_span (by simp)
  have hpT : p∈T := Submodule.subset_span (by simp)
  have hpa : Accessible p := by
    refine ⟨heven p hp,?_,?_⟩
    · intro h;subst p;exact hpn (Submodule.zero_mem _)
    · intro h;subst p;exact hpn (Submodule.subset_span (Set.mem_singleton _))
  have hqa : Accessible q := by
    refine ⟨heven q hq,?_,?_⟩
    · intro h;subst q;exact hqn T.zero_mem
    · intro h;subst q;exact hqn hones
  refine ⟨p,q,hp,hq,hpa,hqa,heven (p+q) (W.add_mem hp hq),?_,?_⟩
  · intro h
    have h' : q=0-p := by apply eq_sub_iff_add_eq.mpr;simpa [add_comm] using h
    exact hqn (h' ▸ T.sub_mem T.zero_mem hpT)
  · intro h
    have h' : q=ones n-p := by apply eq_sub_iff_add_eq.mpr;simpa [add_comm] using h
    exact hqn (h' ▸ T.sub_mem hones hpT)

end
end Holant.ReedMuller.AffineRadon
