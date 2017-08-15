package explicit;

import java.util.BitSet;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.PrimitiveIterator.OfInt;

import common.IterableStateSet;

public interface MDPGeneric<Value> extends NondetModel
{
	/**
	 * Get an iterator over the transitions from choice {@code i} of state {@code s}.
	 */
	public Iterator<Entry<Integer, Value>> getTransitionsIterator(int s, int i);

	/**
	 * Perform a single step of precomputation algorithm Prob0, i.e., for states i in {@code subset},
	 * set bit i of {@code result} iff, for all/some choices,
	 * there is a transition to a state in {@code u}.
	 * Quantification over choices is determined by {@code forall}.
	 * @param subset Only compute for these states
	 * @param u Set of states {@code u}
	 * @param forall For-all or there-exists (true=for-all, false=there-exists)
	 * @param result Store results here
	 */
	public default void prob0step(final BitSet subset, final BitSet u, final boolean forall, final BitSet result)
	{
		for (OfInt it = new IterableStateSet(subset, getNumStates()).iterator(); it.hasNext();) {
			final int s = it.nextInt();
			boolean b1 = forall; // there exists or for all
			for (int choice = 0, numChoices = getNumChoices(s); choice < numChoices; choice++) {
				boolean b2 = someSuccessorsInSet(s, choice, u);
				if (forall) {
					if (!b2) {
						b1 = false;
						break;
					}
				} else {
					if (b2) {
						b1 = true;
						break;
					}
				}
			}
			result.set(s, b1);
		}
	}

	/**
	 * Perform a single step of precomputation algorithm Prob1A, i.e., for states i in {@code subset},
	 * set bit i of {@code result} iff, for all choices,
	 * there is a transition to a state in {@code v} and all transitions go to states in {@code u}.
	 * @param subset Only compute for these states
	 * @param u Set of states {@code u}
	 * @param v Set of states {@code v}
	 * @param result Store results here
	 */
	public default void prob1Astep(BitSet subset, BitSet u, BitSet v, BitSet result)
	{
		boolean b1;
		for (OfInt it = new IterableStateSet(subset, getNumStates()).iterator(); it.hasNext();) {
			final int s = it.nextInt();
			b1 = true;
			for (int choice = 0, numChoices = getNumChoices(s); choice < numChoices; choice++) {
				if (!(successorsSafeAndCanReach(s, choice, u, v))) {
					b1 = false;
					break;
				}
			}
			result.set(s, b1);
		}
	}

	/**
	 * Perform a single step of precomputation algorithm Prob1E, i.e., for states i in {@code subset},
	 * set bit i of {@code result} iff, for some choice,
	 * there is a transition to a state in {@code v} and all transitions go to states in {@code u}.
	 * Optionally, store optimal (memoryless) strategy info for 1 states. 
	 * @param subset Only compute for these states
	 * @param u Set of states {@code u}
	 * @param v Set of states {@code v}
	 * @param result Store results here
	 * @param strat Storage for (memoryless) strategy choice indices (ignored if null)
	 */
	public default void prob1Estep(BitSet subset, BitSet u, BitSet v, BitSet result, int strat[])
	{
		int stratCh = -1;
		boolean b1;
		for (OfInt it = new IterableStateSet(subset, getNumStates()).iterator(); it.hasNext();) {
			final int s = it.nextInt();
			b1 = false;
			for (int choice = 0, numChoices = getNumChoices(s); choice < numChoices; choice++) {
				if (successorsSafeAndCanReach(s, choice, u, v)) {
					b1 = true;
					// If strategy generation is enabled, remember optimal choice
					if (strat != null)
						stratCh = choice;
					break;
				}
			}
			// If strategy generation is enabled, store optimal choice
			// (only if this the first time we add the state to S^yes)
			if (strat != null & b1 & !result.get(s)) {
				strat[s] = stratCh;
			}
			// Store result
			result.set(s, b1);
		}
	}

	/**
	 * Perform a single step of precomputation algorithm Prob1, i.e., for states i in {@code subset},
	 * set bit i of {@code result} iff, for all/some choices,
	 * there is a transition to a state in {@code v} and all transitions go to states in {@code u}.
	 * Quantification over choices is determined by {@code forall}.
	 * @param subset Only compute for these states
	 * @param u Set of states {@code u}
	 * @param v Set of states {@code v}
	 * @param forall For-all or there-exists (true=for-all, false=there-exists)
	 * @param result Store results here
	 */
	public default void prob1step(BitSet subset, BitSet u, BitSet v, boolean forall, BitSet result)
	{
		boolean b1, b2;
		for (OfInt it = new IterableStateSet(subset, getNumStates()).iterator(); it.hasNext();) {
			final int s = it.nextInt();
			b1 = forall; // there exists or for all
			for (int choice = 0, numChoices = getNumChoices(s); choice < numChoices; choice++) {
				b2 = successorsSafeAndCanReach(s, choice, u, v);
				if (forall) {
					if (!b2) {
						b1 = false;
						break;
					}
				} else {
					if (b2) {
						b1 = true;
						break;
					}
				}
			}
			result.set(s, b1);
		}
	}

	/**
	 * Perform a single step of precomputation algorithm Prob1 for a single state/choice,
	 * i.e., return whether there is a transition to a state in {@code v} and all transitions go to states in {@code u}.
	 * @param s State (row) index
	 * @param i Choice index
	 * @param u Set of states {@code u}
	 * @param v Set of states {@code v}
	 */
	public default boolean prob1stepSingle(int s, int i, BitSet u, BitSet v)
	{
		return successorsSafeAndCanReach(s, i, u, v);
	}

}
