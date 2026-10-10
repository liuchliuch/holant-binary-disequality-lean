import Holant.Dihedral.SupportIntegration.NoWeightTwo

/-! Exact original-pair matching projections reconstruct the unique
weight-four word through every triple when weight two is absent. -/
noncomputable section
namespace Holant.Dihedral.SupportIntegration
open Holant.Dihedral.EndpointParallelogram Holant.ReedMuller.LowArity Holant.ReedMuller.Steiner
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 def portPairing {ι : Type*} {r : ℕ} (p : (Fin r × Bool) ≃ ι) : Pairing ι where
  mate i := p ((p.symm i).1,!(p.symm i).2)
  involutive := by intro i; simp
  fixed_free := by
    intro i hh
    have he := congrArg (fun z => (p.symm z).2) hh
    simp only [Equiv.symm_apply_apply] at he
    cases h : (p.symm i).2 <;> simp [h] at he

 theorem matching_edge_word {ι : Type*} [DecidableEq ι] {r : ℕ}
    (p : (Fin r × Bool) ≃ ι) (k : ι) :
    ∀ e,(portPairing p).edgeWord k (p (e,false))=(portPairing p).edgeWord k (p (e,true)) := by
  intro e
  have hh := (portPairing p).edgeWord_mem k (p (e,true))
  simpa [portPairing] using hh

 private theorem bit_one_of_ne_zero (a : ZMod 2) (ha : a ≠ 0) : a=1 := by
  have hh : ∀ a : ZMod 2,a=0 ∨ a=1 := by decide
  exact (hh a).resolve_left ha

 theorem steiner_of_exact_projections (D : BinaryCode n)
    (hP : ExactMatchingProjections D)
    (hno : ∀ x : BinaryVector n,x ∈ D → (support x).card ≠ 2) : SteinerProperty D := by
  classical
  intro i j k hij hik hjk
  obtain ⟨r,p,hp⟩ := hP i j hij
  let k' : Remaining i j := ⟨k,Ne.symm hik,Ne.symm hjk⟩
  let q' := (portPairing p).mate k'
  let q := q'.val
  have hqi : q ≠ i := q'.property.1
  have hqj : q ≠ j := q'.property.2
  have hqk : q ≠ k := by
    intro hh
    apply (portPairing p).fixed_free k'
    exact Subtype.ext hh
  let y := (portPairing p).edgeWord k'
  obtain ⟨x,hx,hijx,hrest⟩ := (hp y).mpr (matching_edge_word p k')
  have hy (l : Fin n) (hli : l ≠ i) (hlj : l ≠ j) :
      x l=if l=k ∨ l=q then 1 else 0 := by
    have hh := hrest ⟨l,hli,hlj⟩
    simpa only [y,Pairing.edgeWord,Subtype.mk.injEq,k',q',q,Subtype.ext_iff] using hh
  have hxi : x i ≠ 0 := by
    intro hz
    have hxj : x j=0 := hijx.symm.trans hz
    have hword : x=indicator {k,q} := by
      funext l
      by_cases hli : l=i
      · subst l
        simp [indicator,hz,hik,Ne.symm hqi]
      · by_cases hlj : l=j
        · subst l
          simp [indicator,hxj,hjk,Ne.symm hqj]
        · rw [hy l hli hlj]
          simp [indicator]
    have hw : (support x).card=2 := by rw [hword,support_indicator]; simp [Ne.symm hqk]
    exact hno x hx hw
  have hi1 : x i=1 := bit_one_of_ne_zero _ hxi
  have hj1 : x j=1 := hijx.symm.trans hi1
  let B : Finset (Fin n) := {i,j,k,q}
  have hword : x=indicator B := by
    funext l
    by_cases hli : l=i
    · subst l; simp [indicator,B,hi1]
    · by_cases hlj : l=j
      · subst l; simp [indicator,B,hj1]
      · rw [hy l hli hlj]
        simp [indicator,B,hli,hlj]
  have hBc : B.card=4 := by simp [B,hij,hik,hjk,Ne.symm hqi,Ne.symm hqj,Ne.symm hqk]
  have hBD : indicator B ∈ D := hword ▸ hx
  refine ⟨B,⟨⟨hBc,hBD⟩,by simp [B],by simp [B],by simp [B]⟩,?_⟩
  intro C hC
  obtain ⟨⟨hCc,hCD⟩,hiC,hjC,hkC⟩ := hC
  have hmatch : ∀ e,indicator C (p (e,false)).val=indicator C (p (e,true)).val := by
    apply (hp (fun l => indicator C l.val)).mp
    exact ⟨indicator C,hCD,by simp [indicator,hiC,hjC],fun _ => rfl⟩
  have hqC : q ∈ C := by
    have he : indicator C q=indicator C k := by
      have hh := hmatch (p.symm k').1
      have hk : p ((p.symm k').1,(p.symm k').2)=k' := by simp
      cases hb : (p.symm k').2
      · have hh' : p ((p.symm k').1,false)=k' := by simpa [hb] using hk
        change indicator C (p ((p.symm k').1,!((p.symm k').2))).val=indicator C k
        simpa only [hb,Bool.not_false,hh'] using hh.symm
      · have hh' : p ((p.symm k').1,true)=k' := by simpa [hb] using hk
        change indicator C (p ((p.symm k').1,!((p.symm k').2))).val=indicator C k
        simpa only [hb,Bool.not_true,hh'] using hh
    have hone : indicator C q=1 := by simpa [indicator,hkC] using he
    simpa [indicator] using hone
  have hsub : B ⊆ C := by
    intro l hl
    simp only [B,Finset.mem_insert,Finset.mem_singleton] at hl
    rcases hl with rfl|rfl|rfl|rfl
    · exact hiC
    · exact hjC
    · exact hkC
    · exact hqC
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

 theorem LocalAtlas.steiner {K : Type*} [Field K] {F : BinaryVector (n+2) → K}
    (A : LocalAtlas F) (hn : 4<n+2) : SteinerProperty A.direction :=
  steiner_of_exact_projections A.direction A.exactMatchingProjections (A.no_weight_two hn)

end Holant.Dihedral.SupportIntegration
