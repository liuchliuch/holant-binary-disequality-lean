import Holant.Pauli.ExoticKlein.SixPortPhysicalCards

/-! Deriving the finite direction/scalar input from actual safe cards after
normalizing one physical base card. No support oracle is assumed. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section

 theorem fillOrdered_base (u v : Bool) (z : Fin 4 → Bool) :
    fillOrdered 0 u v z = Fin.cons u (Fin.cons v z) := by
  funext i
  fin_cases i <;> rfl

 theorem card_base (a : Label) (h : Signature ℂ 6) : card 0 a h = baseCard a h := by
  funext z
  simp only [card,cardOver,baseCard,fillOrdered_base]
  rfl

 theorem exists_prepared_form (h : Signature ℂ 6) (hs : AllPhysicalSafe h)
    (hbase : baseCard 0 h = directionTensor baseDirection) :
    ∃ state : DirectionTriple, ∃ scale : Fin 4 → ℂ,
      Admissible state scale ∧ h = normalizedTensor state scale := by
  classical
  have hordered := (allPhysicalSafe_iff_ordered h).mp hs
  have hchoices (i : Fin 3) : ∃ direction : Option Direction, ∃ scale : ℂ,
      baseCard (labelEquiv i.succ) h = (fun z => scale*optionDirection direction z) ∧
      (if direction.isSome then scale ≠ 0 else scale = 0) := by
    by_cases hz : baseCard (labelEquiv i.succ) h = 0
    · refine ⟨none,0,?_,rfl⟩
      rw [hz]
      funext z
      simp
    · have hc := hordered 0 (labelEquiv i.succ)
      rw [card_base] at hc
      obtain ⟨d,s,he⟩ := hc
      have hs0 : s ≠ 0 := by
        intro hs0
        apply hz
        rw [he,hs0]
        funext z
        simp
      exact ⟨some d,s,he,hs0⟩
  choose directions scales hcards hlive using hchoices
  let scale : Fin 4 → ℂ := Fin.cons 1 scales
  refine ⟨directions,scale,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact one_ne_zero
    · exact hlive j
  · apply normalizedTensor_of_cards h directions scale
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change baseCard (labelEquiv 0) h = fun z => 1*directionTensor baseDirection z
      rw [show labelEquiv 0 = 0 by rfl]
      simpa only [one_mul] using hbase
    · exact hcards j

/-- This isolates the exhaustive finite obligation. The hypothesis must still
be supplied by checked certificate data for EVERY direction triple. -/
theorem normalized_base_product_of_coverage
    (coverage : ∀ state : DirectionTriple, ∃ certificate : LinearCertificate.Certificate 4 64 60 48 960,
      certificate.check (problem state) (initialRows state) = true)
    (h : Signature ℂ 6) (hn : h ≠ 0) (hs : AllPhysicalSafe h)
    (hbase : baseCard 0 h = directionTensor baseDirection) : IsProduct h := by
  obtain ⟨state,scale,ha,he⟩ := exists_prepared_form h hs hbase
  obtain ⟨certificate,hcheck⟩ := coverage state
  rw [he] at hn hs ⊢
  exact normalized_product_of_checked_physical state certificate hcheck scale ha hs hn

end
end Holant.Pauli.ExoticKlein.SixPort
