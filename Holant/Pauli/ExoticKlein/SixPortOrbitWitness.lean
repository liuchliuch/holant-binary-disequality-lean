import Holant.Pauli.ExoticKlein.SixPortOrbitEncoding
import Holant.Pauli.ExoticKlein.SixPortOrbitData

/-! Small numeric word-endpoint checks with proved physical semantic meaning. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def orbitWord (i : Fin 64) : List (Fin 9) :=
  (List.range (orbitWordLengths.get i.val)).map
    (fun j => Fin.ofNat 9 (orbitWordCodes.get i.val / 9^j))

 def representativeCode (i : Fin 4045) : Fin 117649 := Fin.ofNat 117649 (orbitRepresentativeCodes.get i.val)

 def orbitWitnessCheck (source : Fin 117649) (witness : Nat × Nat) : Bool :=
  decide (wordTags (orbitWord (Fin.ofNat 64 witness.2)) (tagStateEquiv source) =
    tagStateEquiv (representativeCode (Fin.ofNat 4045 witness.1)))

 theorem orbitWitness_sound (source : Fin 117649) (witness : Nat × Nat)
    (h : orbitWitnessCheck source witness = true) :
    wordState (orbitWord (Fin.ofNat 64 witness.2)) (stateEquiv source) =
      stateEquiv (representativeCode (Fin.ofNat 4045 witness.1)) := by
  apply tagged_word_endpoint
  exact of_decide_eq_true h

 def orbitSourceCode (block : Fin 920) (i : Fin 128) : Fin 117649 :=
  Fin.ofNat 117649 (128*block.val+i.val)

 def orbitBlockCheck (block : Fin 920) (data : FiniteTable (Nat × Nat)) : Bool :=
  decide (∀ i : Fin 128, orbitWitnessCheck (orbitSourceCode block i) (data.get i.val) = true)

 theorem orbitBlock_sound (block : Fin 920) (data : FiniteTable (Nat × Nat))
    (h : orbitBlockCheck block data = true) (i : Fin 128) :
    wordState (orbitWord (Fin.ofNat 64 (data.get i.val).2)) (stateEquiv (orbitSourceCode block i)) =
      stateEquiv (representativeCode (Fin.ofNat 4045 (data.get i.val).1)) := by
  apply orbitWitness_sound
  exact (of_decide_eq_true h) i

 theorem orbitSourceCode_surjective (source : Fin 117649) :
    ∃ block : Fin 920, ∃ i : Fin 128, orbitSourceCode block i = source := by
  let block : Fin 920 := ⟨source.val/128,by have := source.isLt; omega⟩
  let i : Fin 128 := ⟨source.val%128,Nat.mod_lt _ (by decide)⟩
  refine ⟨block,i,?_⟩
  apply Fin.ext
  change (128*(source.val/128)+source.val%128)%117649 = source.val
  have he : 128*(source.val/128)+source.val%128 = source.val := by omega
  rw [he,Nat.mod_eq_of_lt source.isLt]

/-- Exhaustive checked word endpoints transport solved representatives to
EVERY actual direction triple. This does not count or assert minimal orbits. -/
 theorem all_solved_of_orbit_blocks (data : Fin 920 → FiniteTable (Nat × Nat))
    (checked : ∀ block, orbitBlockCheck block (data block) = true)
    (representatives : ∀ i : Fin 4045, Solved (stateEquiv (representativeCode i))) :
    ∀ state : DirectionTriple, Solved state := by
  intro state
  let source := stateEquiv.symm state
  obtain ⟨block,i,he⟩ := orbitSourceCode_surjective source
  have hw := orbitBlock_sound block (data block) (checked block) i
  rw [he] at hw
  have hs := solved_of_word_representative _ _ _ hw (representatives _)
  simpa only [source,Equiv.apply_symm_apply] using hs

end
end Holant.Pauli.ExoticKlein.SixPort
