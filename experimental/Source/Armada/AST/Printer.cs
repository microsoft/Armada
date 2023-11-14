using System;
using System.IO;
using System.Collections.Generic;

namespace Microsoft.Starmada
{
    public class Printer
    {
        static public string GetFStarHeaderForModule(string moduleName) {
            var str = "";
            str += "module " + moduleName + "\n\n";
            str += "open Armada.Action\n";
            str += "open Armada.Base\n";
            str += "open Armada.Expression\n";
            str += "open Armada.Init\n";
            str += "open Armada.Memory\n";
            str += "open Armada.Program\n";
            str += "open Armada.State\n";
            str += "open Armada.Statement\n";
            str += "open Armada.Type\n";
            str += "open Armada.Pointer\n";
            str += "open Armada.Computation\n";
            str += "open FStar.List.Tot\n";
            str += "open FStar.Char\n";
            str += "open FStar.Sequence.Base\n";
            str += "open Spec.Behavior\n";
            str += "open Spec.Ubool\n";
            return str;
        }

        static public string GetFStarAtomicHeader() {
            string str = "";
            str += "open Strategies.Atomic\n";
            str += "open Strategies.Semantics\n";
            str += "open Strategies.Semantics.Armada\n";
            str += "open Strategies.AtomicToRegular.Armada\n";
            str += "open Strategies.RegularToAtomic.Armada\n";
            str += "open Strategies.PCIndices\n";
            str += "open Util.ImmutableArray\n";
            str += "open Util.Nth\n";
            return str;
        }

        static public string GetFStarProofHeader(ProofDecl proof) {
            string str = "";
            if (proof.Strategy is WeakeningStrategy)
            {
                str += "open Armada.Transition\n";
                str += "open FStar.List.Tot.Base\n";
                str += "open FStar.Tactics\n";
                str += "open Spec.List\n";
                str += "open Strategies.Atomic\n";
                str += "open Strategies.Invariant\n";
                str += "open Strategies.Invariant.Armada.Atomic\n";
                str += "open Strategies.Semantics\n";
                str += "open Strategies.Semantics.Armada\n";
                str += "open Strategies.Weakening.Armada\n";
                str += "open Util.Behavior\n";
                str += "open Util.ImmutableArray\n";
                str += "open Util.List\n";
            }
            else if (proof.Strategy is VarIntroStrategy)
            {
                str += "open Armada.Thread\n";
                str += "open Armada.Transition\n";
                str += "open Strategies.ArmadaStatement.ThreadState\n";
                str += "open Strategies.Atomic\n";
                str += "open Strategies.GlobalVars.Types\n";
                str += "open Strategies.Semantics\n";
                str += "open Strategies.Semantics.Armada\n";
                str += "open Strategies.PCIndices\n";
                str += "open Strategies.VarIntro.Defs\n";
                str += "open Strategies.VarIntro.Efficient\n";
                str += "open Util.ImmutableArray\n";
            }
            else if (proof.Strategy is VarHidingStrategy)
            {
                str += "open Armada.Thread\n";
                str += "open Armada.Transition\n";
                str += "open Strategies.ArmadaStatement.ThreadState\n";
                str += "open Strategies.Atomic\n";
                str += "open Strategies.GlobalVars\n";
                str += "open Strategies.GlobalVars.Types\n";
                str += "open Strategies.Nonyielding\n";
                str += "open Strategies.Semantics\n";
                str += "open Strategies.Semantics.Armada\n";
                str += "open Strategies.PCIndices\n";
                str += "open Strategies.VarHiding.Defs\n";
                str += "open Strategies.VarHiding.Efficient\n";
                str += "open Util.ImmutableArray\n";
            }
            return str;
        }

        static public string GetFStarInvariantHeader(ProofDecl proof) {
            string str = "";
            if (proof == null) {
                str += "open Armada.Step\n";
                str += "open Armada.Transition\n";
                str += "open Strategies.Atomic\n";
                str += "open Strategies.GlobalVars\n";
                str += "open Strategies.GlobalVars.Types\n";
                str += "open Strategies.Invariant\n";
                str += "open Strategies.Invariant.Armada\n";
                str += "open Strategies.Invariant.Armada.Atomic\n";
                str += "open Strategies.Semantics\n";
                str += "open Strategies.Semantics.Armada\n";
                str += "open Spec.List\n";
                str += "open Spec.Ubool\n";
                str += "open Util.List\n";

                str += "open Strategies.ArmadaInvariant.PositionsValid\n";
                str += "open Strategies.ArmadaInvariant.RootsMatch\n";
                str += "open Strategies.GlobalVars\n";
                str += "open Strategies.GlobalVars.Init\n";
                str += "open Strategies.GlobalVarsProof\n";
                str += "open Strategies.GlobalVars.UnaddressedStatement\n";
            }
            else if (proof.Strategy is VarIntroStrategy || proof.Strategy is VarHidingStrategy)
            {
                str += "open Armada.Step\n";
                str += "open Armada.Transition\n";
                str += "open Strategies.Atomic\n";
                str += "open Strategies.GlobalVars.Types\n";
                str += "open Strategies.Invariant\n";
                str += "open Strategies.Invariant.Armada\n";
                str += "open Strategies.Invariant.Armada.AtomicSubstep\n";
                str += "open Strategies.Semantics\n";
                str += "open Strategies.Semantics.Armada\n";
                str += "open Spec.List\n";
                str += "open Spec.Ubool\n";
                str += "open Util.List\n";
            }
            else if (proof.Strategy is WeakeningStrategy)
            {
                str += "open Armada.Transition\n";
                str += "open FStar.List.Tot.Base\n";
                str += "open FStar.Tactics\n";
                str += "open Spec.List\n";
                str += "open Strategies.Atomic\n";
                str += "open Strategies.Invariant\n";
                str += "open Strategies.Invariant.Armada.Atomic\n";
                str += "open Strategies.Semantics\n";
                str += "open Strategies.Semantics.Armada\n";
                str += "open Strategies.Weakening.Armada\n";
                str += "open Util.Behavior\n";
                str += "open Util.ImmutableArray\n";
                str += "open Util.List\n";
            }
            return str;
        }

        static public string GetFStarProofHeader(ProofDecl proof, string L, string H) {
            string str = GetFStarProofHeader(proof);
            str += $"open AtomicToRegularRefinement{H}\n";
            str += $"open RegularToAtomicRefinement{L}\n";
            if (proof.Strategy is WeakeningStrategy) {
                str += $"open Invariant{L}{H}\n";
            }
            return str;
        }
    }
}
