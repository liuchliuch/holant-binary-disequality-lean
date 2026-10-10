import Holant.Pauli.ExoticKlein.SixPortNormalizeLemmas

/-! Actual base-card normalization by three local exotic dressings, a physical
port permutation, and a nonzero scalar. The inverse operations preserve genuine
matching products. Exhaustive finite certificate coverage remains separate. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem normalize_base_kernel (h : Signature ℂ 6) (hn : h ≠ 0) (hs : AllPhysicalSafe h) :
    ∃ g : Signature ℂ 6, AllPhysicalSafe g ∧ g ≠ 0 ∧ baseCard 0 g ≠ 0 ∧
      (IsProduct g → IsProduct h) := by
  obtain ⟨a,ha⟩ := exists_nonzero_baseCard h hn
  obtain ⟨c,hc,he⟩ := baseCard_local_first a 0 h
  simp only [add_zero] at he
  refine ⟨localAction 0 a h,allPhysicalSafe_localAction h hs 0 a,localAction_ne_zero 0 a h hn,?_,?_⟩
  · intro hz
    apply ha
    funext z
    have hh := congrFun (hz.symm.trans he) z
    change 0 = c*baseCard a h z at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hc
  · exact isProduct_of_localAction h 0 a

 theorem normalize_base_matching (h : Signature ℂ 6) (hn : h ≠ 0) (hs : AllPhysicalSafe h)
    (hb : baseCard 0 h ≠ 0) :
    ∃ g : Signature ℂ 6, ∃ a b : Label, ∃ s : ℂ, s ≠ 0 ∧ AllPhysicalSafe g ∧ g ≠ 0 ∧
      baseCard 0 g = (fun z => s*directionTensor (0,a,b) z) ∧ (IsProduct g → IsProduct h) := by
  obtain ⟨⟨m,a,b⟩,s,he⟩ := baseCard_onDirection h hs 0
  have hs0 : s ≠ 0 := by
    intro hz
    apply hb
    rw [he,hz]
    funext z
    simp
  let e := extendResidual (straightenMatching m)
  refine ⟨Tensor.reindex e h,a,b,s,hs0,allPhysicalSafe_reindex e h hs,reindex_ne_zero e h hn,?_,?_⟩
  · rw [baseCard_reindex_residual,he]
    funext z
    change s*Tensor.reindex (straightenMatching m) (directionTensor (m,a,b)) z = _
    rw [straighten_direction]
  · exact isProduct_of_reindex e h

 theorem normalize_base_labels (h : Signature ℂ 6) (hn : h ≠ 0) (hs : AllPhysicalSafe h)
    (a b : Label) (s : ℂ) (hs0 : s ≠ 0)
    (hb : baseCard 0 h = fun z => s*directionTensor (0,a,b) z) :
    ∃ g : Signature ℂ 6, AllPhysicalSafe g ∧ g ≠ 0 ∧ baseCard 0 g = directionTensor baseDirection ∧
      (IsProduct g → IsProduct h) := by
  let h1 := localAction 2 a h
  have hs1 : AllPhysicalSafe h1 := allPhysicalSafe_localAction h hs 2 a
  have hn1 : h1 ≠ 0 := localAction_ne_zero 2 a h hn
  have hb1 : baseCard 0 h1 = fun z => (s*omega a a)*directionTensor (0,0,b) z := by
    change baseCard 0 (localAction (0 : Fin 4).succ.succ a h) = _
    rw [baseCard_local_remaining (0 : Fin 4) a 0 h,hb]
    change localMatrix 0 (E a) (fun z => s*directionTensor (0,a,b) z) = _
    rw [localMatrix_scale_tensor]
    change (fun z => s*localAction (0 : Fin 4) a (directionTensor (0,a,b)) z) = _
    rw [base_cancel_first]
    funext z
    ring
  let h2 := localAction 4 b h1
  have hs2 : AllPhysicalSafe h2 := allPhysicalSafe_localAction h1 hs1 4 b
  have hn2 : h2 ≠ 0 := localAction_ne_zero 4 b h1 hn1
  let q := s*omega a a*omega b b
  have hq : q ≠ 0 := mul_ne_zero (mul_ne_zero hs0 (omega_ne_zero a a)) (omega_ne_zero b b)
  have hb2 : baseCard 0 h2 = fun z => q*directionTensor (0,0,0) z := by
    change baseCard 0 (localAction (2 : Fin 4).succ.succ b h1) = _
    rw [baseCard_local_remaining (2 : Fin 4) b 0 h1,hb1]
    change localMatrix 2 (E b) (fun z => (s*omega a a)*directionTensor (0,0,b) z) = _
    rw [localMatrix_scale_tensor]
    change (fun z => (s*omega a a)*localAction (2 : Fin 4) b (directionTensor (0,0,b)) z) = _
    rw [base_cancel_second]
    funext z
    dsimp [q]
    ring
  refine ⟨(fun x => q⁻¹*h2 x),allPhysicalSafe_scale h2 hs2 q⁻¹,
    scale_ne_zero h2 hn2 q⁻¹ (inv_ne_zero hq),?_,?_⟩
  · rw [baseCard_scale,hb2]
    funext z
    change q⁻¹*(q*directionTensor (0,0,0) z) = directionTensor baseDirection z
    rw [← mul_assoc,inv_mul_cancel₀ hq,one_mul]
    rfl
  · intro hp
    have hp2 : IsProduct h2 := isProduct_of_scale h2 q⁻¹ (inv_ne_zero hq) hp
    have hp1 : IsProduct h1 := isProduct_of_localAction h1 4 b hp2
    exact isProduct_of_localAction h 2 a hp1

/-- Every nonzero tensor satisfying the actual safe-card hypothesis admits the
source's exact base-card normalization, with proved product descent. -/
 theorem exists_normalization (h : Signature ℂ 6) (hn : h ≠ 0) (hs : AllPhysicalSafe h) :
    ∃ g : Signature ℂ 6, AllPhysicalSafe g ∧ g ≠ 0 ∧ baseCard 0 g = directionTensor baseDirection ∧
      (IsProduct g → IsProduct h) := by
  obtain ⟨h1,hs1,hn1,hb1,descend1⟩ := normalize_base_kernel h hn hs
  obtain ⟨h2,a,b,s,hs0,hs2,hn2,hb2,descend2⟩ := normalize_base_matching h1 hn1 hs1 hb1
  obtain ⟨g,hsg,hng,hbg,descend3⟩ := normalize_base_labels h2 hn2 hs2 a b s hs0 hb2
  exact ⟨g,hsg,hng,hbg,fun hp => descend1 (descend2 (descend3 hp))⟩

/-- The full six-port result reduces to the explicit exhaustive finite checker
obligation. No such coverage theorem is assumed elsewhere or claimed here. -/
 theorem six_port_product_of_coverage
    (coverage : ∀ state : DirectionTriple, ∃ certificate : LinearCertificate.Certificate 4 64 60 48 960,
      certificate.check (problem state) (initialRows state) = true)
    (h : Signature ℂ 6) (hn : h ≠ 0) (hs : AllPhysicalSafe h) : IsProduct h := by
  obtain ⟨g,hsg,hng,hbg,descend⟩ := exists_normalization h hn hs
  exact descend (normalized_base_product_of_coverage coverage g hng hsg hbg)

end
end Holant.Pauli.ExoticKlein.SixPort
