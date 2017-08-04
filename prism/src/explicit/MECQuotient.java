//==============================================================================
//	
//	Copyright (c) 2017-
//	Authors:
//	* Joachim Klein <klein@tcs.inf.tu-dresden.de> (TU Dresden)
//	
//------------------------------------------------------------------------------
//	
//	This file is part of PRISM.
//	
//	PRISM is free software; you can redistribute it and/or modify
//	it under the terms of the GNU General Public License as published by
//	the Free Software Foundation; either version 2 of the License, or
//	(at your option) any later version.
//	
//	PRISM is distributed in the hope that it will be useful,
//	but WITHOUT ANY WARRANTY; without even the implied warranty of
//	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//	GNU General Public License for more details.
//	
//	You should have received a copy of the GNU General Public License
//	along with PRISM; if not, write to the Free Software Foundation,
//	Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
//	
//==============================================================================

package explicit;

import java.util.BitSet;
import java.util.List;

import common.IterableBitSet;
import explicit.modelviews.EquivalenceRelationInteger;
import explicit.modelviews.MDPDroppedChoicesCached;
import explicit.modelviews.MDPEquiv;
import explicit.modelviews.MDPEquiv.StateChoicePair;
import prism.PrismComponent;
import prism.PrismDevNullLog;
import prism.PrismException;

/**
 * Helper class for obtaining the MEC (maximal end-component) quotient of an MDP.
 * <br>
 * In the original MDP, the maximal end components are identified, i.e.,
 * those end components where there is a strategy to stay infinitely, and where
 * every other state of the end component can be reached with probability 1.
 * <br>
 * In the quotient, those MECs are each collapsed to a single state,
 * with choices that have transitions outside the MEC preserved.
 * The non-representative states remain in the MDP, but become trap-states.
 * <br>
 * Additionally, a set of 'yes' and 'no' states can be given, which are
 * also collapsed to a single state, respectively.
 */
public class MECQuotient extends PrismComponent
{
	/** The original model (stored for strategy lifting) */
	private MDP originalModel;
	/** The quotient model, with all MECs collapsed */
	private MDPEquiv quotient;
	/** The equivalence relation for state indices in the same MEC */
	private EquivalenceRelationInteger equiv;
	/** The MDP where all actions that lead back to the same MEC are removed (stored for strategy lifting) */
	private MDPDroppedChoicesCached ecSelfloopsDroppedMDP;
	/** The set of 'yes' states in the original model */
	private BitSet yes;
	/** The set of 'no' states in the original model */
	private BitSet no;

	private static final boolean debug = true;

	/**
	 * @param parent the parent PrismComponent
	 * @param originalModel The original model (stored for strategy lifting)
	 * @param quotient The quotient model, with all MECs collapsed
	 * @param equiv The equivalence relation for state indices in the same MEC
	 * @param ecSelfloopsDroppedMDP The MDP where all actions that lead back to the same MEC are removed (stored for strategy lifting)
	 * @param yes The set of 'yes' states in the original model
	 * @param no The set of 'no' states in the original model
	 */
	private MECQuotient(PrismComponent parent, MDP originalModel, MDPEquiv quotient, EquivalenceRelationInteger equiv, MDPDroppedChoicesCached ecSelfloopsDroppedMDP, BitSet yes, BitSet no)
	{
		super(parent);
		this.originalModel = originalModel;
		this.quotient = quotient;
		this.equiv = equiv;
		this.ecSelfloopsDroppedMDP = ecSelfloopsDroppedMDP;
		this.yes = yes;
		this.no = no;
	}

	/** Get the quotient model */
	public MDP getModel()
	{
		return quotient;
	}

	/**
	 * Get the non-representative states in the quotient model,
	 * i.e., states that have been mapped to the representative for their MEC.
	 * These states remain in the quotient model, but are trap states.
	 */
	public BitSet getNonRepresentativeStates()
	{
		return quotient.getNonRepresentativeStates();
	}

	/**
	 * Get the 'yes' states in the quotient model, i.e., the representative for the yes states.
	 */
	public BitSet getYesInQuotient()
	{
		// yesInQuotient is the representative for the yes equivalence class
		BitSet yesInQuotient = new BitSet();
		yesInQuotient.set(quotient.mapStateToRestrictedModel(yes.nextSetBit(0)));
		return yesInQuotient;
	}

	/**
	 * Get the 'no' states in the quotient model, i.e., the representative for the no states
	 * and the non-representative states (trap states).
	 */
	public BitSet getNoInQuotient()
	{
		// noInQuotient is the representative for the no equivalence class as well
		// as the non-representative states (the states in any equivalence class
		// that are not the representative for the class). As the latter states
		// are traps, we can just add them to the no set
		BitSet noInQuotient = new BitSet();
		noInQuotient.set(quotient.mapStateToRestrictedModel(no.nextSetBit(0)));
		noInQuotient.or(quotient.getNonRepresentativeStates());
		return noInQuotient;
	}

	/**
	 * Map results from the quotient model to the original model.
	 * <br>
	 * For all the non-representative states, store the value computed
	 * for the representative for their MEC.
	 */
	public void mapResults(double[] soln) {
		for (int s : new IterableBitSet(quotient.getNonRepresentativeStates())) {
			int representative = quotient.mapStateToRestrictedModel(s);
			soln[s] = soln[representative];
		}
	}

	/**
	 * Lift a strategy from the quotient model to the original model.
	 * <br>
	 * For each MEC, compute the target state and choice in the original model,
	 * i.e., lookup the state and choice corresponding to the choice selected
	 * at the representative in the quotient model.
	 * <br>
	 * Then, for the other MEC states, compute a probability one strategy of
	 * reaching this target state.
	 * <br>
	 * Modifies {@code strat} to be a strategy in the original model.
	 * @param strat the strategy in the quotient model (will be changed)
	 */
	public void liftStrategy(int[] strat) throws PrismException
	{
		// construct MDP model checker, for prob1e strategy computations
		MDPModelChecker mc = new MDPModelChecker(this);
		// silence prob1e output...
		mc.setLog(new PrismDevNullLog());

		for (int i = 0; i < equiv.getNumClasses(); i++) {
			BitSet ec = equiv.getIthEquivalenceClass(i);
			int representative = equiv.getRepresentativeForIthEquivalenceClass(i);

			// don't lift strategy for yes or no states
			if (yes.get(representative) || no.get(representative)) {
				continue;
			}

			if (debug)
				getLog().println("Class " + i + ": " + ec + ", representative is " + representative);

			int stratChoice = strat[representative];

			int targetState;
			int targetChoice;
			if (stratChoice < 0) {
				// -1 = unknown, -2 = arbitrary
				// we will use the representative as the target state
				targetState = representative;
				targetChoice = stratChoice;  // keep same choice
			} else {
				StateChoicePair choice = quotient.mapToOriginalModelOrNull(representative, stratChoice);
				if (choice == null) {
					targetState = representative;
					targetChoice = stratChoice;
				} else {
					targetState = choice.getState();
					targetChoice = choice.getChoice();
				}

				// map back via dropped choices
				targetChoice = ecSelfloopsDroppedMDP.mapChoiceToOriginalModel(targetState, targetChoice);
			}

			if (debug)
				getLog().println("Strat choice is " + stratChoice + ", target = " + targetState + ", targetChoice = " + targetChoice);

			BitSet target = new BitSet();
			target.set(targetState);

			// compute prob1e strategy to target state
			// for the states in this EC (remain = ec, goal = target)
			BitSet prob1inEC = mc.prob1(originalModel, ec, target, false, strat);

			assert(prob1inEC.equals(ec));

			// target state gets the target choice
			strat[targetState] = targetChoice;
		}
	}

	/**
	 * Get the maximal end component quotient for the given MDP.
	 * <br>
	 * Additionally, a set of yes and no states is collapsed to a single state, respectively, as well.
	 * @param parent the parent PrismComponent
	 * @param mdp the MDP
	 * @param yes a subset of states known to be 'yes' states (may be empty)
	 * @param no a subset of states known to be 'no' states (may be empty)
	 * @return the quotient
	 */
	public static MECQuotient getQuotient(PrismComponent parent, MDP mdp, BitSet yes, BitSet no) throws PrismException
	{
		// compute states that are not yes / no states
		BitSet maybe = new BitSet();
		maybe.set(0, mdp.getNumStates());
		maybe.andNot(yes);
		maybe.andNot(no);

		ECComputer ec = ECComputer.createECComputer(parent, mdp);

		// compute MECs in maybe set (not yes/no states)
		ec.computeMECStates(maybe);
		List<BitSet> mecs = ec.getMECStates();

		// if yes is non-empty, add as an equivalence class
		if (!yes.isEmpty())
			mecs.add(yes);

		// if no is non-empty, add as an equivalence class
		if (!no.isEmpty())
			mecs.add(no);

		EquivalenceRelationInteger eq = new EquivalenceRelationInteger(mecs);

		// construct MDP view where all choices that would lead back to the same MEC
		// are dropped
		final MDPDroppedChoicesCached ecSelfloopsDropped = new MDPDroppedChoicesCached(mdp,
				(int state, int choice) -> {
					// drop choice if all successors are again in the same equivalence class
					return mdp.allSuccessorsMatch(state, choice, (int target) -> {
						return eq.test(state, target);
					});
				});

		// compute quotient
		MDPEquiv quotient = new MDPEquiv(ecSelfloopsDropped, eq);

		int realStates = quotient.getNumStates() - quotient.getNonRepresentativeStates().cardinality();
		parent.getLog().println("MEC-Quotient MDP: " + realStates + " equivalence classes / non-trap states.");

		if (debug) {
			quotient.exportToDotFile("mec-quotient.dot");
		}

		return new MECQuotient(parent, mdp, quotient, eq, ecSelfloopsDropped, yes, no);
	}

}
