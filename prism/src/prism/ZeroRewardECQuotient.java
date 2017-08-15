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

package prism;

import java.io.FileNotFoundException;
import java.util.List;

import jdd.JDD;
import jdd.JDDNode;
import mtbdd.PrismMTBDD;
import prism.PrismComponent;
import prism.PrismException;
import sparse.PrismSparse;

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
	private MDPQuotient quotient;

	/** The transformed relevant state rewards in the quotient model */
	private JDDNode quotientStateRew;

	/** The transformed relevant transition rewards in the quotient model */
	private JDDNode quotientTransRew;

	/** The number of collapsed zero-reward ECs */
	private int numberOfZMECs;

	private static final boolean debug = false;

	/**
	 * Private constructor, called from static getQuotient method.
	 * @param parent the parent PrismComponent
	 * @param quotient the quotient
	 * @param quotientStateRew the transformed relevant state rewards
	 * @param quotientTransRew the transformed relevant transition rewards
	 * @param numberOfZMECs the number of zero-reward MECs
	 */
	private ZeroRewardECQuotient(PrismComponent parent, MDPQuotient quotient, JDDNode quotientStateRew, JDDNode quotientTransRew, int numberOfZMECs)
	{
		super(parent);
		this.quotient = quotient;
		this.quotientStateRew = quotientStateRew;
		this.quotientTransRew = quotientTransRew;
		this.numberOfZMECs = numberOfZMECs;
	}

	public void clear()
	{
		quotient.clear();
		JDD.Deref(quotientStateRew);
		JDD.Deref(quotientTransRew);
	}

	public NondetModel getQuotientModel()
	{
		return quotient.getTransformedModel();
	}

	public JDDNode getQuotientStateRew()
	{
		return quotientStateRew;
	}

	public JDDNode getQuotientTransRew()
	{
		return quotientTransRew;
	}

	public int getNumberOfZMECs()
	{
		return numberOfZMECs;
	}

	/** Map the given state set from the original model to the quotient model */
	public JDDNode mapStateSetToQuotient(JDDNode S) {
		return quotient.mapStateSetToQuotient(S);
	}

	public StateValues projectToOriginalModel(StateValues svTransformedModel) throws PrismException
	{
		return quotient.projectToOriginalModel(svTransformedModel);
	}

	/**
	 * Construct a sub-MDP consisting of the zero-reward fragment:<br>
	 * States with positive reward or having only positive-reward choices become deadlock states,
	 * positive-reward choices on zero-reward states are dropped.
	 * @param mdp the original MDP
	 * @param restrict only consider this state set
	 * @param stateRew the state rewards
	 * @param transRew the transition rewards
	 * <br>[ REFS: <i>result</i>, DEREFS: <i>none</i> ]
	 */
	public static ZeroRewardFragmentMDP getZeroRewardFragment(NondetModel mdp, JDDNode restrict, JDDNode stateRew, JDDNode transRew) throws PrismException
	{
		return ZeroRewardFragmentMDP.from(mdp, restrict, stateRew, transRew);
	}

	public static class ZeroRewardFragmentMDP {
		private NondetModel fragmentMdp;
		private JDDNode posRewardStates;

		/**
		 * Constructor.
		 * <br>[ STORES: fragmentMdp, posRewardStates ]
		 */
		private ZeroRewardFragmentMDP(NondetModel fragmentMdp, JDDNode posRewardStates)
		{
			this.fragmentMdp = fragmentMdp;
			this.posRewardStates = posRewardStates;
		}

		/** Clear stored model / state information */
		public void clear()
		{
			fragmentMdp.clear();
			fragmentMdp = null;
			JDD.Deref(posRewardStates);
			posRewardStates = null;
		}

		/**
		 * Get the zero-reward fragment model (not a copy).
		 */
		public NondetModel getNondetModel()
		{
			return fragmentMdp;
		}

		/**
		 * Get the positive reward states, i.e., those states that
		 * have positive state reward or only positive-reward actions.
		 * <br>[ REFS: <i>result</i> ]
		 */
		public JDDNode getPositiveRewardStates()
		{
			return posRewardStates.copy();
		}

		/**
		 * Get the zero reward states, i.e., those states that
		 * have no state reward and at least one outgoing zero-reward action.
		 * <br>[ REFS: <i>result</i> ]
		 */
		public JDDNode getZeroRewardStates()
		{
			return JDD.And(fragmentMdp.getReach().copy(), JDD.Not(posRewardStates.copy()));
		}

		/**
		 * Build the zero-reward fragment of an MDP. Positive-reward states become deadlock states
		 */
		private static ZeroRewardFragmentMDP from(NondetModel mdp, final JDDNode restrict, final JDDNode stateRew, final JDDNode transRew) throws PrismException
		{

			class ZeroRewardTransformation extends NondetModelTransformationOperator {
				private JDDNode tr01ZeroRew;
				private JDDNode statesWithZeroRewChoice;
				private JDDNode posRewardStates;

				public ZeroRewardTransformation(NondetModel model)
				{
					super(model);

					// Compute zero-reward transitions, i.e., those that
					// leave a zero-reward state and have no reward.
					// Note: this assumes that transition rewards are
					// of the form
					//     rew(s,choice) = reward
					// and not of the form
					//     rew(s,choice,t) = reward,
					// i.e., that transition rewards are identical for
					// a given state choice pair
					tr01ZeroRew = JDD.Equals(transRew.copy(), 0.0);
					tr01ZeroRew = JDD.And(tr01ZeroRew, JDD.Equals(stateRew.copy(), 0.0));
					tr01ZeroRew = JDD.And(tr01ZeroRew, restrict.copy());
					tr01ZeroRew = JDD.And(tr01ZeroRew, model.getTrans01().copy());

					// find states with at least one zero-reward transition
					statesWithZeroRewChoice = JDD.ThereExists(tr01ZeroRew.copy(), model.getAllDDColVars());
					statesWithZeroRewChoice = JDD.ThereExists(statesWithZeroRewChoice, model.getAllDDNondetVars());

					// compute states that necessarily incur a positive reward
					// these state become deadlocks in the transformed model
					posRewardStates = JDD.And(model.getReach().copy(), JDD.Not(statesWithZeroRewChoice.copy()));
				}

				public void clear()
				{
					super.clear();
					JDD.Deref(tr01ZeroRew, statesWithZeroRewChoice, posRewardStates);
				}

				@Override
				public int getExtraStateVariableCount()
				{
					return 0;
				}

				@Override
				public int getExtraActionVariableCount()
				{
					return 0;
				}

				@Override
				public JDDNode getTransformedTrans()
				{
					return JDD.Times(originalModel.getTrans().copy(), tr01ZeroRew.copy());
				}

				@Override
				public JDDNode getTransformedStart()
				{
					return statesWithZeroRewChoice.copy();
				}

				@Override
				public JDDNode getReachableStates()
				{
					return originalModel.getReach().copy();
				}

				@Override
				public boolean deadlocksAreFine()
				{
					return true;
				}
			}

			ZeroRewardTransformation transformation = new ZeroRewardTransformation(mdp);
			NondetModel transformed = mdp.getTransformed(transformation);

			for (int i = 0; i < transformed.getNumRewardStructs(); i++) {
				transformed.resetStateRewards(i, JDD.ZERO.copy());
				transformed.resetTransRewards(i, JDD.ZERO.copy());
			}

			ZeroRewardFragmentMDP zeroRewardFragmentMDP = new ZeroRewardFragmentMDP(transformed, transformation.posRewardStates.copy());
			transformation.clear();

			return zeroRewardFragmentMDP;
		}
	};

	/**
	 * Compute the states that have a zero-reward strategy, i.e.,
	 * that can remain in a subset of the MDP indefinitely without
	 * ever accumulating reward.
	 *
	 * @param parent the parent PrismComponent (for settings)
	 * @param mdp the MDP
	 * @param restrict consider this subset of states
	 * @param rewards the MDP rewards
	 * @return the set of states with a zero-reward strategy
	 */
	public static JDDNode computeZeroRewStrategyStates(PrismComponent parent, NondetModel mdp, JDDNode restrict, JDDNode stateRew, JDDNode transRew) throws PrismException
	{
		ZeroRewardFragmentMDP zeroRew = getZeroRewardFragment(mdp, restrict, stateRew, transRew);
		NondetModel zeroRewMDP = zeroRew.getNondetModel();

		JDDNode avoid = zeroRew.getPositiveRewardStates();

		// compute set of states that have a strategy to infinitely avoid the positive reward states,
		// i.e., a strategy of indefinitely taking only zero-reward choices
		//  = prob0e(all, avoid)
		JDDNode zeroRewStrategyStates =
				PrismMTBDD.Prob0E(zeroRewMDP.getTrans01(),
				                  zeroRewMDP.getReach(),
				                  zeroRewMDP.getNondetMask(),
				                  zeroRewMDP.getAllDDRowVars(),
				                  zeroRewMDP.getAllDDColVars(),
				                  zeroRewMDP.getAllDDNondetVars(),
				                  zeroRewMDP.getReach(),
				                  avoid);

		JDD.Deref(avoid);
		zeroRew.clear();

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
	public static ZeroRewardECQuotient getQuotient(PrismComponent parent, NondetModel mdp, JDDNode restrict, JDDNode stateRew, JDDNode transRew) throws PrismException
	{
		ZeroRewardFragmentMDP zeroRew = getZeroRewardFragment(mdp, restrict, stateRew, transRew);
		NondetModel zeroRewMDP = zeroRew.getNondetModel();

		JDDNode avoid = zeroRew.getPositiveRewardStates();

		// compute set of states that have a strategy to infinitely avoid the positive reward states,
		// i.e., a strategy of indefinitely taking only zero-reward choices
		//  = prob0e(all, avoid)
		JDDNode zeroRewStrategyStates =
				PrismMTBDD.Prob0E(zeroRewMDP.getTrans01(),
				                  zeroRewMDP.getReach(),
				                  zeroRewMDP.getNondetMask(),
				                  zeroRewMDP.getAllDDRowVars(),
				                  zeroRewMDP.getAllDDColVars(),
				                  zeroRewMDP.getAllDDNondetVars(),
				                  zeroRewMDP.getReach(),
				                  avoid);

		JDD.Deref(avoid);

		if (zeroRewStrategyStates.equals(JDD.ZERO)) {
			JDD.Deref(zeroRewStrategyStates);
			zeroRew.clear();

			return null;
		}

		// we have to build the quotient

		JDDNode remain = zeroRew.getZeroRewardStates();

		ECComputer ecComputer = ECComputer.createECComputer(parent, zeroRewMDP);
		ecComputer.computeMECStates(zeroRewStrategyStates);
		List<JDDNode> mecs = ecComputer.getMECStates();

		JDD.Deref(zeroRewStrategyStates);
		zeroRew.clear();

		MDPQuotient quotient = MDPQuotient.transform(parent, mdp, mecs, remain.copy());
		JDDNode quotientStateRew = quotient.getTransformedStateReward(stateRew);
		JDDNode quotientTransRew = quotient.getTransformedTransReward(transRew);

		JDD.Deref(remain);

		if (debug) {
			try {
				quotient.getTransformedModel().exportToFile(Prism.EXPORT_DOT, true, new java.io.File("zero-mec-quotient.dot"));

				PrismMTBDD.ExportVector(quotientStateRew, "state rewards", quotient.getTransformedModel().getAllDDRowVars(), quotient.getTransformedModel().getODD(), Prism.EXPORT_PLAIN, "zero-mec-quotient.srew");
				PrismSparse.ExportSubMDP(quotient.getTransformedModel().getTrans(),
				                         quotientTransRew,
				                         "trans rewards",
				                         quotient.getTransformedModel().getAllDDRowVars(),
				                         quotient.getTransformedModel().getAllDDColVars(),
				                         quotient.getTransformedModel().getAllDDNondetVars(),
				                         quotient.getTransformedModel().getODD(),
				                         Prism.EXPORT_PLAIN,
				                         "zero-mec-quotient.trew");
			} catch (FileNotFoundException e) {}
		}

		return new ZeroRewardECQuotient(parent, quotient, quotientStateRew, quotientTransRew, mecs.size());
	}

}
