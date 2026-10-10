import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasBase

/-! Exact finite case slice of the preserved v2 atlas. All witness leaves are
unchanged; splitting the matching selectors bounds elaboration per module. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant
namespace Proportional.AtlasCases

theorem pp_0_0 (ae be ao bo e0 e1 o0 o1 : Bool)
    (evenNonempty : e0=true ∨ e1=true) (oddNonempty : o0=true ∨ o1=true)
    (relation : (ae ^^ be)=(!(ao ^^ bo)))
    (doubled : (e0=true ∧ e1=true) ∨ (o0=true ∧ o1=true)) :
    ∃ i j : Fin 6, ∃ p : Bool,
      ProjectionOverflow (PPSupport 0 0 ae be ao bo
        (fun z => if z then e1 else e0) (fun z => if z then o1 else o0)) i j p := by
  cases ae
  · cases be
    · cases ao
      · cases bo
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,2,false,by decide⟩
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,2,false,by decide⟩
            · cases o0
              · cases o1
                · simp_all
                · exact ⟨0,2,false,by decide⟩
              · cases o1
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
      · cases bo
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,4,false,by decide⟩
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,4,false,by decide⟩
            · cases o0
              · cases o1
                · simp_all
                · exact ⟨0,4,false,by decide⟩
              · cases o1
                · exact ⟨0,4,false,by decide⟩
                · exact ⟨0,4,false,by decide⟩
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
    · cases ao
      · cases bo
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,2,false,by decide⟩
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,2,false,by decide⟩
            · cases o0
              · cases o1
                · simp_all
                · exact ⟨0,2,false,by decide⟩
              · cases o1
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
      · cases bo
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,4,false,by decide⟩
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,4,false,by decide⟩
            · cases o0
              · cases o1
                · simp_all
                · exact ⟨0,4,false,by decide⟩
              · cases o1
                · exact ⟨0,4,false,by decide⟩
                · exact ⟨0,4,false,by decide⟩
  · cases be
    · cases ao
      · cases bo
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,4,false,by decide⟩
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,4,false,by decide⟩
            · cases o0
              · cases o1
                · simp_all
                · exact ⟨0,4,false,by decide⟩
              · cases o1
                · exact ⟨0,4,false,by decide⟩
                · exact ⟨0,4,false,by decide⟩
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
      · cases bo
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,2,false,by decide⟩
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,2,false,by decide⟩
            · cases o0
              · cases o1
                · simp_all
                · exact ⟨0,2,false,by decide⟩
              · cases o1
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
    · cases ao
      · cases bo
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,4,false,by decide⟩
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,4,false,by decide⟩
            · cases o0
              · cases o1
                · simp_all
                · exact ⟨0,4,false,by decide⟩
              · cases o1
                · exact ⟨0,4,false,by decide⟩
                · exact ⟨0,4,false,by decide⟩
      · cases bo
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,2,false,by decide⟩
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · exact ⟨0,2,false,by decide⟩
            · cases o0
              · cases o1
                · simp_all
                · exact ⟨0,2,false,by decide⟩
              · cases o1
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
        · cases e0
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
          · cases e1
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all
            · cases o0
              · cases o1
                · simp_all
                · simp_all
              · cases o1
                · simp_all
                · simp_all

end Proportional.AtlasCases
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
