using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;

namespace Microsoft.Starmada
{
    class ProofPrinter
    {
        public Dictionary<string, string> GetProofs(LevelDecl L, int indentation)
        {
            var Capitalized = (string s) => char.ToUpper(s[0]) + s.Substring(1);
            var levelName = Capitalized(L.Name.ToString(0, false));
            Dictionary<string, string> proofs = new();

            foreach (var inv in L.Invariants) {
                var invName = Capitalized(inv.Name.ToString(0, false));
                var moduleName = "Invariant" + levelName + invName;
                var invariantHeader = Printer.GetFStarHeaderForModule(moduleName);
                invariantHeader += Printer.GetFStarInvariantHeader(null);
                var invariantStr = InvariantPrinter.GetProof(L, inv, indentation) + "\n";
                proofs[moduleName] = invariantHeader + '\n' + invariantStr;
            }
            return proofs;
        }
        // Return a module name => content
        public Dictionary<string, string> GetProofs(ProofDecl proof, LevelDecl L, LevelDecl H, int indentation)
        {
            var Capitalized = (string s) => char.ToUpper(s[0]) + s.Substring(1);
            var moduleNameLow = Capitalized(L.Name.ToString(0, false));
            var moduleNameHigh = Capitalized(H.Name.ToString(0, false));
            var moduleName = "Proof" + moduleNameLow + moduleNameHigh;

            StrategyPrinter p;
            string invariantName = "";
            if (proof.Strategy is WeakeningStrategy)
            {
                invariantName = "Invariant" + moduleNameLow + moduleNameHigh;
                p = new WeakeningPrinter();
            }
            else if (proof.Strategy is VarIntroStrategy)
            {
                invariantName = "Atomic" + moduleNameHigh + "Invariant";
                p = new VarIntroPrinter();
            }
            else if (proof.Strategy is VarHidingStrategy)
            {
                invariantName = "Atomic" + moduleNameLow + "Invariant";
                p = new VarHidingPrinter();
            }
            else
            {
                throw new NotImplementedException();
            }

            Dictionary<string, string> proofs = new();
            var header = Printer.GetFStarHeaderForModule(moduleName);
            header += Printer.GetFStarProofHeader(proof, moduleNameLow, moduleNameHigh);
            proofs[moduleName] = header + '\n' + p.GetProof(proof, L, H, indentation);

            var invariantHeader = Printer.GetFStarHeaderForModule(invariantName);
            invariantHeader += Printer.GetFStarInvariantHeader(proof);
            var invariantStr = p.GetInvariant(proof, L, H, 0) + "\n";
            proofs[invariantName] = invariantHeader + '\n' + invariantStr;
            return proofs;
        }
    }

    interface StrategyPrinter
    {
        string GetProof(ProofDecl proof, LevelDecl L, LevelDecl H, int indentation);
        string GetInvariant(ProofDecl proof, LevelDecl L, LevelDecl H, int indentation);
    }
}