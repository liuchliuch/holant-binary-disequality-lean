import Holant.Proofs.Algorithms.TransformRecognition.RawAffineBranchMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalCatalogueSource


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineBranchSource
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
variable {s : ℕ} (arity : Fin s → ℕ)

noncomputable def fromSource (input : OriginalFamilyInput.Input arity) (disequality : Bool)
    (B : AffineBranch.Branch arity) : RawAffineBranchMachine.Input :=
  (OriginalFamilyPackingSource.fromSource arity input disequality,
    List.ofFn (fun i => RationalAffineTemplateSource.sourceCode (B.1 i)),
    RationalAffineTemplateSource.sourceCode B.2)

theorem family_exact (input : OriginalFamilyInput.Input arity) (disequality : Bool) :
    (OriginalFamilyPackingSource.fromSource arity input disequality).1 =
      OriginalCatalogueSource.family arity input := rfl

theorem imaginary_exact (input : OriginalFamilyInput.Input arity) (disequality : Bool)
    (B : AffineBranch.Branch arity) :
    RawAffineBranchMachine.imaginary (fromSource arity input disequality B) =
      (OriginalAffineSystem.imaginaryVariable arity).val := by
  simp only [RawAffineBranchMachine.imaginary,fromSource,OriginalFamilyPackingMachine.base,
    OriginalFamilyPackingMachine.parameterCount,OriginalFamilyPackingSource.family_length,
    OriginalFamilyPackingSource.original_length,OriginalAffineSystem.imaginaryVariable,
    OriginalVariableLayout.special,Fin.val_natAdd]
  omega

theorem vertex_exact (input : OriginalFamilyInput.Input arity) (disequality : Bool)
    (B : AffineBranch.Branch arity) (i : Fin s) :
    RawAffineBranchMachine.vertexBlock (fromSource arity input disequality B) i.val =
      OriginalAffineBodySource.vertexBlock arity B i := by
  simp only [RawAffineBranchMachine.vertexBlock,fromSource,
    OriginalFamilyPackingMachine.parameterCount,OriginalFamilyPackingSource.family_length,
    family_exact,OriginalCatalogueSource.family_length,Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn]
  rw [show i.val=OriginalCatalogueSource.slotNumber (.inl i) from rfl,
    OriginalCatalogueSource.table_exact]
  rfl

theorem edge_exact (input : OriginalFamilyInput.Input arity) (disequality : Bool)
    (B : AffineBranch.Branch arity) :
    RawAffineBranchMachine.edgeBlock (fromSource arity input disequality B) =
      OriginalAffineBodySource.edgeBlock arity B := by
  simp only [RawAffineBranchMachine.edgeBlock,fromSource,
    OriginalFamilyPackingMachine.parameterCount,OriginalFamilyPackingSource.family_length,family_exact,OriginalCatalogueSource.family_length]
  have ht := OriginalCatalogueSource.table_exact arity input (.inr ())
  simp only [OriginalCatalogueSource.slotNumber] at ht
  rw [ht]
  rfl

theorem body_exact (input : OriginalFamilyInput.Input arity) (disequality : Bool)
    (B : AffineBranch.Branch arity) :
    RawAffineBranchMachine.bodyInput (fromSource arity input disequality B) =
      OriginalAffineBodySource.encode arity B := by
  have hv : (List.range s).map (RawAffineBranchMachine.vertexBlock (fromSource arity input disequality B)) =
      (List.finRange s).map (OriginalAffineBodySource.vertexBlock arity B) := by
    change CommonFieldMachine.Coordinates.tab s
      (RawAffineBranchMachine.vertexBlock (fromSource arity input disequality B)) = _
    rw [CommonFieldMachine.Coordinates.tab_ofFn,List.ofFn_eq_map]
    exact List.map_congr_left (fun i _ => vertex_exact arity input disequality B i)
  change (OriginalFamilyPackingMachine.width (OriginalFamilyPackingSource.fromSource arity input disequality),
    RawAffineBranchMachine.imaginary (fromSource arity input disequality B),
    RawAffineBranchMachine.imaginary (fromSource arity input disequality B)+1,
    RawAffineBranchMachine.imaginary (fromSource arity input disequality B)+2,
    (List.range (OriginalFamilyPackingSource.fromSource arity input disequality).1.length).map
      (RawAffineBranchMachine.vertexBlock (fromSource arity input disequality B)),
    RawAffineBranchMachine.edgeBlock (fromSource arity input disequality B)) = _
  rw [OriginalFamilyPackingSource.width_exact,imaginary_exact,
    OriginalFamilyPackingSource.family_length,hv,edge_exact]
  simp only [OriginalAffineBodySource.encode,OriginalAffineSystem.imaginaryVariable,
    OriginalAffineSystem.sqrtVariable,OriginalAffineSystem.eighthVariable,
    OriginalVariableLayout.special,Fin.val_natAdd]
  congr 2 <;> omega

theorem request_exact (input : OriginalFamilyInput.Input arity) (disequality : Bool)
    (B : AffineBranch.Branch arity) :
    RawAffineBranchMachine.request (fromSource arity input disequality B) =
      OriginalAffineBranchMachine.fromSource arity (OriginalFamilyInput.pack arity input disequality) B := by
  unfold RawAffineBranchMachine.request
  rw [body_exact]
  simp only [fromSource,OriginalFamilyPackingSource.roots_exact,
    OriginalFamilyPackingSource.addresses_exact,OriginalAffineBranchMachine.fromSource]

/-- A valid original representation suffices to derive an actual finite run;
no precomputed transformed coefficients, equation body or successful answer
is given to the source machine. -/
theorem source_outputs (input : OriginalFamilyInput.Input arity)
    (hv : OriginalFamilyInput.Valid arity input) (disequality : Bool)
    (B : AffineBranch.Branch arity) :
    ∃ bound, Nonempty (TM2OutputsInTime RawAffineBranchMachine.machine.computer
      (RawAffineBranchMachine.encoding.encode (fromSource arity input disequality B))
      (some (encodingBoolBool.encode (OriginalAffineDecision.branchAnswer arity
        (OriginalFamilyInput.pack arity input disequality)
        (OriginalFamilyInput.pack_valid arity input hv disequality) B))) bound) := by
  obtain ⟨bound,⟨run⟩⟩ := OriginalAffineBranchMachine.source_outputs arity
    (OriginalFamilyInput.pack arity input disequality)
    (OriginalFamilyInput.pack_valid arity input hv disequality) B
  have prepared := RawAffineBranchMachine.prepare.outputs (fromSource arity input disequality B)
  rw [request_exact] at prepared
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ prepared run⟩⟩

end Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineBranchSource
