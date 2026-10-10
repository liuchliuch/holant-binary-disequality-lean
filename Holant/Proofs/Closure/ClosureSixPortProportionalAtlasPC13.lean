import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasBase

/-! Exact finite case slice of the preserved v2 atlas. All witness leaves are
unchanged; splitting the matching selectors bounds elaboration per module. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant
namespace Proportional.AtlasCases

theorem pc_1_3 (ap bp f0 f1 sector a b o : Bool)
    (nonempty : f0=true ∨ f1=true) (relation : (ap ^^ bp)=(!(a ^^ b))) :
    ∃ i j : Fin 6, ∃ p : Bool,
      ProjectionCertificate (PCSupport 1 ap bp (fun z => if z then f1 else f0)
        sector 3 a b o) i j p := by
  cases ap
  · cases bp
    · cases f0
      · cases f1
        · cases sector
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
        · cases sector
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
      · cases f1
        · cases sector
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
        · cases sector
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
              · cases o
                · simp_all
                · simp_all
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
              · cases o
                · simp_all
                · simp_all
    · cases f0
      · cases f1
        · cases sector
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
        · cases sector
          · cases a
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
          · cases a
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
      · cases f1
        · cases sector
          · cases a
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
          · cases a
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
        · cases sector
          · cases a
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
          · cases a
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
  · cases bp
    · cases f0
      · cases f1
        · cases sector
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
        · cases sector
          · cases a
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
          · cases a
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
      · cases f1
        · cases sector
          · cases a
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
          · cases a
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
        · cases sector
          · cases a
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
          · cases a
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
    · cases f0
      · cases f1
        · cases sector
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · simp_all
                · simp_all
        · cases sector
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
      · cases f1
        · cases sector
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,false,by decide⟩
              · cases o
                · simp_all
                · simp_all
        · cases sector
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
              · cases o
                · simp_all
                · simp_all
          · cases a
            · cases b
              · cases o
                · simp_all
                · simp_all
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
            · cases b
              · cases o
                · exact ⟨0,2,false,by decide⟩
                · exact ⟨0,2,true,by decide⟩
              · cases o
                · simp_all
                · simp_all

end Proportional.AtlasCases
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
