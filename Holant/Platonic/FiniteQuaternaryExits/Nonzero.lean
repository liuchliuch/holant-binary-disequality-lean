import Holant.Certificates.PlatonicQuaternaryExits.SourceClauses

namespace Holant.Platonic.FiniteQuaternaryExits
open Holant Holant.Certificates Holant.Certificates.PlatonicQuaternaryExits
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem network_zero_of_vertex {K : Type*} [CommSemiring K] {n : ℕ}
    (N : Network K n) (v : Fin N.shape.vertices) (hv : ∀x,N.vertex v x=0) :
    N.denote=0 := by
  classical
  funext x
  unfold Network.denote
  apply Finset.sum_eq_zero
  intro z _
  have hp : (∏ w,N.vertex w (N.shape.assignment x z w))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ v) (hv _)
  rw [hp,zero_mul]

theorem bounded_zero {D : Direction} {n : ℕ} {q : Signature ℂ 4} {t : Signature ℂ n}
    (h : BoundedRealization D q t) (hq : q=0) : t=0 := by
  classical
  obtain ⟨N,hN,hv,_,hcount,_⟩ := h
  have hn : 0<(Finset.univ.filter (fun v => N.shape.arity v=4)).card := by omega
  obtain ⟨v,hv⟩ := Finset.card_pos.mp hn
  have harity := (Finset.mem_filter.mp hv).2
  have hmem : (⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈resources D q := by
    exact ‹∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈resources D q› v
  have hzero : ∀x,N.vertex v x=0 := by
    rcases hmem with he|⟨B,he,_⟩
    · have hh := congrArg (fun f : AnySignature ℂ => ∀x,f.2 x=0) he
      exact hh.mpr (by simp [hq])
    · have hh := congrArg Sigma.fst he
      simp only [harity] at hh
      norm_num at hh
  rw [←hN]
  exact network_zero_of_vertex N v hzero

theorem source_signature_nonzero (s : SourceCase) : s.signature≠0 := by
  intro hz
  rcases all_platonic_quaternary_exits s with ⟨t,ht,hE,_⟩ | ⟨t,ht,hE⟩ | ⟨B,hB,hd,_⟩
  · have ht0 := bounded_zero ht hz
    exact hE.2.1 (by rw [ht0]; rfl)
  · have ht0 := bounded_zero ht hz
    exact hE.1 (by rw [ht0]; rfl)
  · have hB0 := bounded_zero hB hz
    have hzero : B=0 := by
      funext a b
      have he := congrFun hB0 (![a,b] : Fin 2 → Bool)
      simpa only [OctahedralSeparator.Native.binarySignature,Matrix.cons_val_zero,
        Matrix.cons_val_one,Pi.zero_apply] using he
    apply hd
    rw [hzero]
    norm_num
end
end Holant.Platonic.FiniteQuaternaryExits
