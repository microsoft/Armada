using System.Linq;

namespace Microsoft.Armada
{
  public class PrioritizationAttributes
  {
    public int likelihoodOfFailure;

    public override string ToString()
    {
      return $"{{:likelihood_of_failure {likelihoodOfFailure}}}";
    }
  }

  public class Prioritizer
  {
    public static PrioritizationAttributes GetPrioritizationAttributesForLiftAtomicPath(AtomicPath lowAtomicPath, AtomicPath highAtomicPath)
    {

        if (lowAtomicPath.NextRoutines.Select(nextRoutine => nextRoutine.armadaStatement == null ? null : Printer.StatementToString(nextRoutine.armadaStatement.Stmt)).SequenceEqual(
          highAtomicPath.NextRoutines.Select(nextRoutine => nextRoutine.armadaStatement == null ? null : Printer.StatementToString(nextRoutine.armadaStatement.Stmt))))
        {
            return new PrioritizationAttributes { likelihoodOfFailure = 0 };
        }

      return new PrioritizationAttributes { likelihoodOfFailure = 3 };

      /*
      // TODO: this check assumes that corresponding nextRoutines with no associated armada statements are the same
      if (lowAtomicPath.NextRoutines.Count == highAtomicPath.NextRoutines.Count)
      {
        bool stmtsEqual = false;
        for (int i = 0; i < lowAtomicPath.NextRoutines.Count; i++) {
          if (stmtsEqual) {
            return new PrioritizationAttributes { likelihoodOfFailure = 0 };
          }
        }
      }
      return new PrioritizationAttributes { likelihoodOfFailure = 3 };
      */
    }
  }

}
