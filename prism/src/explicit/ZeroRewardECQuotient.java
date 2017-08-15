//==============================================================================
//	
//	Copyright (c) 2016-
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

import java.util.Arrays;
import java.util.BitSet;
import java.util.List;

import common.functions.primitive.PairPredicateInt;
import common.IterableBitSet;
import explicit.graphviz.Decorator;
import explicit.graphviz.ShowRewardDecorator;
import explicit.modelviews.EquivalenceRelationInteger;
import explicit.modelviews.MDPDroppedChoicesCached;
import explicit.modelviews.MDPEquiv;
import explicit.modelviews.MDPEquiv.StateChoicePair;
import explicit.rewards.MDPRewards;
import prism.PrismComponent;
import prism.PrismDevNullLog;
import prism.PrismException;

/**
 * Helper class for obtaining the zero-reward EC quotient of an MDP.
 * <br>
 * In the original MDP, the zero-reward maximal end components are identified, i.e.,
 * those end components where there is a strategy to stay infinitely without ever
 * seeing another reward.
 * <br>
 * In the quotient, those zero-reward MECs are each collapsed to a single state,
 * with choices that have transitions outside the MEC preserved.
 */
public class ZeroRewardECQuotient extends PrismComponent
{
	/** The quotient model, with all zero-reward MECs collapsed */
	private MDPEquiv quotient;
	/** The transformed reward structure for the quotient model */
	private MDPRewards quotientRewards;
	/** The equivalence relation for state indices in the same MEC */
	private EquivalenceRelationInteger equiv;
	/** The zero-reward sub-MDP of the original model (stored for strategy lifting) */
	private MDPDroppedChoicesCached zeroRewMDP;
	/** The MDP where all zero-reward action that lead back to the same MEC are removed (stored for strategy lifting) */
	private MDPDroppedChoicesCached droppedZeroRewardLoops;
	/** The number of zero-reward MECs */
	private int numberOfZMECs;

	private static final boolean debug = false;

	/**
	 * Private constructor, called from static getQuotient method.
	 * @param parent the parent PrismComponent
	 * @param quotient The quotient model, with all zero-reward MECs collapsed
	 * @param quotientRewards The transformed reward structure for the quotient model
	 * @param equiv The equivalence relation for state indices in the same MEC
	 * @param zeroRewMDP The zero-reward sub-MDP of the original model
	 * @param droppedZeroRewardLoops The MDP where all zero-reward action that lead back to the same MEC are removed
	 * @param numberOfZMECs The number of zero-reward MECs
	 */
	private ZeroRewardECQuotient(PrismComponent parent, MDPEquiv quotient, MDPRewards quotientRewards, EquivalenceRelationInteger equiv, MDPDroppedChoicesCached zeroRewMDP, MDPDroppedChoicesCached droppedZeroRewardLoops, int numberOfZMECs)
	{
		super(parent);
		this.quotient = quotient;
		this.quotientRewards = quotientRewards;
		this.equiv = equiv;
		this.zeroRewMDP = zeroRewMDP;
		this.droppedZeroRewardLoops = droppedZeroRewardLoops;
		this.numberOfZMECs = numberOfZMECs;
	}

	/** Get the quotient model */
	public MDP getModel()
	{
		return quotient;
	}

	/** Get the rewards for the quotient model */
	public MDPRewards getRewards()
	{
		return quotientRewards;
	}

	/** Get the number of zero-reward MECs */
	public int getNumberOfZeroRewardMECs()
	{
		return numberOfZMECs;
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
	 * reaching this target state, taking only zero-reward actions.
	 * <br>
	 * Modifies {@code strat} to be a strategy in the original model.
	 * @param strat the strategy in the quotient model (will be changed)
	 */
	public void liftStrategy(int[] strat) throws PrismException
	{
		// the states in zero-reward ECs
		BitSet ecs = new BitSet();
		// the target states in the ECs, i.e., those where the
		// computed strategy leaves the EC (at least with positive probability)
		BitSet targetStatesInEcs = new BitSet();

		for (int i = 0; i < equiv.getNumClasses(); i++) {
			BitSet ec = equiv.getIthEquivalenceClass(i);
			int representative = equiv.getRepresentativeForIthEquivalenceClass(i);

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
				targetChoice = droppedZeroRewardLoops.mapChoiceToOriginalModel(targetState, targetChoice);
			}

			if (debug)
				getLog().println("Strat choice is " + stratChoice + ", target = " + targetState + ", targetChoice = " + targetChoice);

			ecs.or(ec);
			targetStatesInEcs.set(targetState);
			strat[targetState] = targetChoice;
		}


		// compute prob1e strategy to EC target states *in the zero-reward fragment MDP*
		// for the states in a zero-reward EC, remaining in the zero-reward ECs
		// as all states are in a zero-reward EC, they have a probability 1 strategy
		// for reaching at least one of the target states
		// construct MDP model checker, for prob1e strategy computations
		MDPModelChecker mc = new MDPModelChecker(this);
		// silence prob1e output...
		mc.setSilentPrecomputations(true);
		BitSet prob1inEC = mc.prob1(zeroRewMDP, ecs, targetStatesInEcs, false, strat); // prob1e

		assert(prob1inEC.equals(ecs));

		// we now have to lift the choices from the zeroRewMDP to the original MDP
		for (int s : IterableBitSet.getSetBits(ecs)) {
			// skip target states
			if (targetStatesInEcs.get(s))
				continue;

			// map choice in zeroRewMDP back to original MDP
			strat[s] = zeroRewMDP.mapChoiceToOriginalModel(s, strat[s]);
		}
	}

	/**
	 * Compute the states that have a zero-reward strategy, i.e.,
	 * that can remain in a subset of the MDP indefinitely without
	 * ever accumulating reward. Optionally, computes the strategy.
	 *
	 * @param parent the parent PrismComponent (for settings)
	 * @param mdp the MDP
	 * @param rewards the MDP rewards
	 * @param strat if non-{@code null}, array for storing the strategy choices
	 * @return the set of states with a zero-reward strategy
	 */
	public static BitSet computeZeroRewStrategyStates(PrismComponent parent, MDP mdp, MDPRewards rewards, int[] strat) throws PrismException
	{
		PairPredicateInt positiveRewardChoice = (int s, int i) -> {
			if (rewards.getStateReward(s) > 0)
				return true;
			if (rewards.getTransitionReward(s, i) > 0) {
				return true;
			}
			return false;
		};

		// drop positive reward choices
		MDPDroppedChoicesCached zeroRewMDP = new MDPDroppedChoicesCached(mdp, positiveRewardChoice);

		// identify states that do not have any choices left
		//  -> states where we'd have to take a positive reward choice
		//     or which are positive reward states
		BitSet trapStates = new BitSet();
		for (int i = 0, n = mdp.getNumStates(); i < n; i++) {
			if (zeroRewMDP.getNumChoices(i) == 0) {
				trapStates.set(i);
			}
		}

		// construct MDP model checker, for prob0e computation
		MDPModelChecker mc = new MDPModelChecker(parent);
		mc.setSilentPrecomputations(true);

		// compute set of states that have a strategy to infinitely avoid the trapStates,
		// i.e., a strategy of indefinitely taking only zero-reward choices
		//  = prob0e(all, trapStates)
		BitSet zeroRewStrategyStates = mc.prob0(zeroRewMDP, null, trapStates, true, strat);

		if (strat != null) {
			// first, convert -2 (don't care) choices into a zero-rew choice for states that also have positive reward choices
			for (int s : IterableBitSet.getSetBits(zeroRewStrategyStates)) {
				if (strat[s] == -2 && zeroRewMDP.getNumChoices(s) != mdp.getNumChoices(s)) {
					strat[s] = 0;  // choice 0 exists, otherwise the state would have been a trap state
				}
			}

			// lift strategy from the zero-reward sub-MDP to the original MDP
			zeroRewMDP.liftStrategy(strat);
		}

		return zeroRewStrategyStates;
	}

	/**
	 * Get the zero-reward end component quotient for the given MDP and reward structure,
	 * or {@code null} if there are no zero-reward end components.
	 * @param parent the parent PrismComponent
	 * @param mdp the MDP
	 * @param restrict a subset of states
	 * @param rewards the reward structure
	 * @return the quotient, or {@code null} if there are no zero-reward end components.
	 */
	public static ZeroRewardECQuotient getQuotient(PrismComponent parent, MDP mdp, BitSet restrict, MDPRewards rewards) throws PrismException
	{
		PairPredicateInt positiveRewardChoice = (int s, int i) -> {
			if (rewards.getStateReward(s) > 0)
				return true;
			if (rewards.getTransitionReward(s, i) > 0) {
				return true;
			}
			return false;
		};

		// drop positive reward choices
		MDPDroppedChoicesCached zeroRewMDP = new MDPDroppedChoicesCached(mdp, positiveRewardChoice);
		// compute the MECs in the zero-reward sub-MDP
		ECComputer ecComputer = ECComputerDefault.createECComputer(parent, zeroRewMDP);
		ecComputer.computeMECStates(restrict);

		List<BitSet> mecs = ecComputer.getMECStates();

		// there are no end components in the zero-reward sub-MDP, return null
		if (mecs.isEmpty()) {
			return null;
		}

		// the equivalence relation on the states
		EquivalenceRelationInteger equiv = new EquivalenceRelationInteger.KeepSingletons(mecs);

		// we drop zero reward loops on the equivalence classes
		PairPredicateInt zeroRewardECloop = (int s, int i) -> {
			// don't drop choices for states outside of restrict
			if (!restrict.get(s))
				return false;

			if (positiveRewardChoice.test(s, i)) {
				return false;
			}

			// return true if all successors t of state s for choice i are in the
			// same equivalence class
			boolean rv = mdp.allSuccessorsMatch(s, i, (int t) -> equiv.test(s,t));
			return rv;
		};

		final MDPDroppedChoicesCached droppedZeroRewardLoops = new MDPDroppedChoicesCached(mdp, zeroRewardECloop);
		if (debug)
			droppedZeroRewardLoops.exportToDotFile("zero-mec-loops-dropped.dot");

		final MDPEquiv quotient = new MDPEquiv(droppedZeroRewardLoops, equiv);

		MDPRewards quotientRewards = new MDPRewards() {
			@Override
			public double getStateReward(int s)
			{
				return rewards.getStateReward(s);
			}

			@Override
			public double getTransitionReward(int s, int i)
			{
				StateChoicePair mapped = quotient.mapToOriginalModel(s, i);
				int mappedChoiceInOriginal = droppedZeroRewardLoops.mapChoiceToOriginalModel(mapped.getState(), mapped.getChoice());
				return rewards.getTransitionReward(mapped.getState(), mappedChoiceInOriginal);
			}

			@Override
			public MDPRewards liftFromModel(Product<? extends Model> product)
			{
				throw new RuntimeException("Not implemented");
			}

			@Override
			public boolean hasTransitionRewards()
			{
				return rewards.hasTransitionRewards();
			}
		};

		if (debug) {
			List<Decorator> decorators = Arrays.asList(new ShowRewardDecorator(quotientRewards));
			quotient.exportToDotFile("zero-mec-quotient.dot", decorators);
		}

		return new ZeroRewardECQuotient(parent, quotient, quotientRewards, equiv, zeroRewMDP, droppedZeroRewardLoops, mecs.size());
	}

}
