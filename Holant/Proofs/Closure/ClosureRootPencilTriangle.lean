import Holant.Proofs.Closure.ClosureRootPencilAffine

/-! The exceptional three-root support triangle is impossible for genuine
phase-three products. Zero entries and every global product scalar are kept;
the contradiction uses actual ratios of supported coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
open Holant Holant.Projective

/-- Three four-word products cannot form the support symmetric-difference
triangle on a projective line when all supported ratios are cube roots. -/
theorem triangle_impossible (f g h : Signature ℂ 4)
    (hf : RootProduct 3 f) (hg : RootProduct 3 g) (hh : RootProduct 3 h)
    (lam mu : ℂ) (hlam : lam ≠ 0) (hmu : mu ≠ 0)
    (relation : h = lam • f + mu • g)
    (union_card : (support f ∪ support g).card = 6) : False := by
  classical
  obtain ⟨F⟩ := hf
  obtain ⟨G⟩ := hg
  obtain ⟨H⟩ := hh
  let S := support f
  let T := support g
  let O := (S \ T) ∪ (T \ S)
  have sCard : S.card=4 := F.support_card
  have tCard : T.card=4 := G.support_card
  have intersection : (S ∩ T).card=2 := by
    have hc := Finset.card_union_add_card_inter S T
    change (S ∪ T).card=6 at union_card
    omega
  have leftCard : (S \ T).card=2 := by
    rw [Finset.card_sdiff,Finset.inter_comm,intersection,sCard]
  have rightCard : (T \ S).card=2 := by
    rw [Finset.card_sdiff,intersection,tCard]
  have outside_disjoint : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have outsideCard : O.card=4 := by
    dsimp only [O]
    rw [Finset.card_union_of_disjoint outside_disjoint,leftCard,rightCard]
  have outsideSubset : O ⊆ support h := by
    intro x hx
    have eq := congrFun relation x
    change h x=lam*f x+mu*g x at eq
    apply (mem_support h x).mpr
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hxf,hxg⟩ := Finset.mem_sdiff.mp hx
      have hn : f x ≠ 0 := (mem_support f x).mp hxf
      have hz : g x=0 := not_ne_iff.mp (fun h => hxg ((mem_support g x).mpr h))
      rw [eq,hz,mul_zero,add_zero]
      exact mul_ne_zero hlam hn
    · obtain ⟨hxg,hxf⟩ := Finset.mem_sdiff.mp hx
      have hn : g x ≠ 0 := (mem_support g x).mp hxg
      have hz : f x=0 := not_ne_iff.mp (fun h => hxf ((mem_support f x).mpr h))
      rw [eq,hz,mul_zero,zero_add]
      exact mul_ne_zero hmu hn
  have outsideExact : O=support h :=
    Finset.eq_of_subset_of_card_le outsideSubset (by rw [H.support_card,outsideCard])
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < (S \ T).card)
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (by omega : 0 < (T \ S).card)
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0 < (S ∩ T).card)
  have hxf : f x ≠ 0 := (mem_support f x).mp (Finset.mem_sdiff.mp hx).1
  have hxg : g x=0 := not_ne_iff.mp (fun h => (Finset.mem_sdiff.mp hx).2
    ((mem_support g x).mpr h))
  have hyg : g y ≠ 0 := (mem_support g y).mp (Finset.mem_sdiff.mp hy).1
  have hyf : f y=0 := not_ne_iff.mp (fun h => (Finset.mem_sdiff.mp hy).2
    ((mem_support f y).mpr h))
  have hzf : f z ≠ 0 := (mem_support f z).mp (Finset.mem_inter.mp hz).1
  have hzg : g z ≠ 0 := (mem_support g z).mp (Finset.mem_inter.mp hz).2
  have hxh : h x ≠ 0 := (mem_support h x).mp (outsideSubset (Finset.mem_union_left _ hx))
  have hyh : h y ≠ 0 := (mem_support h y).mp (outsideSubset (Finset.mem_union_right _ hy))
  have hzh : h z=0 := by
    apply not_ne_iff.mp
    intro hn
    have ho : z ∈ O := outsideExact.symm ▸ (mem_support h z).mpr hn
    rcases Finset.mem_union.mp ho with ho | ho
    · exact (Finset.mem_sdiff.mp ho).2 (Finset.mem_inter.mp hz).2
    · exact (Finset.mem_sdiff.mp ho).2 (Finset.mem_inter.mp hz).1
  have ex : h x=lam*f x := by
    have he := congrFun relation x
    simpa [hxg] using he
  have ey : h y=mu*g y := by
    have he := congrFun relation y
    simpa [hyf] using he
  have cancel : lam*f z+mu*g z=0 := by
    have he := congrFun relation z
    simpa [hzh] using he.symm
  have ratio : h x / h y = - ((f x / f z) * (g z / g y)) := by
    rw [ex,ey]
    field_simp [hmu,hyg,hzf]
    linear_combination cancel
  have hr := H.ratio_roots x y hxh hyh
  have hfR := F.ratio_roots x z hxf hzf
  have hgR := G.ratio_roots z y hzg hyg
  rw [ratio] at hr
  have minus : (- ((f x / f z) * (g z / g y)))^3 = -1 := by
    calc
      (- ((f x / f z) * (g z / g y)))^3 =
          - ((f x / f z)^3 * (g z / g y)^3) := by ring
      _ = -1 := by rw [hfR,hgR];norm_num
  rw [minus] at hr
  norm_num at hr

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
