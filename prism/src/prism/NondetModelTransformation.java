//==============================================================================
//	
//	Copyright (c) 2015-
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

import jdd.JDD;
import jdd.JDDNode;
import jdd.JDDVars;

/**
 * Description of a transformation for a NondetModel (MDP).
 * The transformation can request the allocation of extra state and action variables,
 * and specify new transition matrix, initial states and reward information.
 * <br>
 * After use, the transformation should be cleared by calling {@code clear()}.
 */
public abstract class NondetModelTransformation
{
	protected NondetModel originalModel;
	protected JDDVars extraRowVars;
	protected JDDVars extraColVars;
	protected JDDVars extraActionVars;

	/**
	 * Constructor with the original model that is to be transformed.
	 * The original model is not changed and will not be cleared when
	 * {@code clear()} is called.
	 */
	public NondetModelTransformation(NondetModel model)
	{
		originalModel = model;
	}

	/** Clear the transformation */
	public void clear()
	{
		if (extraRowVars != null) {
			extraRowVars.derefAll();
		}
		if (extraColVars != null) {
			extraColVars.derefAll();
		}
		if (extraActionVars != null) {
			extraActionVars.derefAll();
		}
	}

	/** Return the name for any new extra state variables */
	public String getExtraStateVariableName()
	{
		return "extra";
	}

	/** Return the name for any new extra action variables */
	public String getExtraActionVariableName()
	{
		return "tau";
	}

	/** Get the number of needed extra state variables for the transformation.
	 *  This is the number n of state variables, will lead to the allocation of
	 *  2*n variables, n row and n column variables */
	public abstract int getExtraStateVariableCount();

	/** Get the number of needed extra action variables for the transformation. */
	public abstract int getExtraActionVariableCount();

	/**
	 * This method is called to notify the transformation about the state variables
	 * that were allocated.
	 * <br>
	 * The extraRowVars and extraColVars are copies, i.e., this method is responsible
	 * to ensure that they will be derefed eventually.
	 * <br>[ STORES: extraRowVars, extraColVars ]
	 */
	public void hookExtraStateVariableAllocation(JDDVars extraRowVars, JDDVars extraColVars)
	{
		this.extraRowVars = extraRowVars;
		this.extraColVars = extraColVars;
	}

	/**
	 * This method is called to notify the transformation about the action variables
	 * that were allocated.
	 * <br>
	 * The extraActionsVars are copies, i.e., this method is responsible
	 * to ensure that they will be derefed eventually.
	 * <br>[ STORES: extraActionVars ]
	 */
	public void hookExtraActionVariableAllocation(JDDVars extraActionVars)
	{
		this.extraActionVars = extraActionVars;
	}

	/**
	 * Get the transformed transition function.
	 * <br>[ REFS: <i>result</i>, DEREFS: <i>none</i> ]
	 */
	public abstract	JDDNode getTransformedTrans() throws PrismException;

	/**
	 * Get the transformed start function.
	 * <br>[ REFS: <i>result</i>, DEREFS: <i>none</i> ]
	 */
	public abstract JDDNode getTransformedStart() throws PrismException;

	/**
	 * Get the transformed state reward relation, given the old reward relation.
	 * <br>[ REFS: <i>result</i>, DEREFS: <i>none</i> ]
	 */
	public JDDNode getTransformedStateReward(JDDNode oldReward) throws PrismException
	{
		JDD.Ref(oldReward);
		return oldReward;
	}

	/**
	 * Get the transformed transition reward relation, given the old reward relation.
	 * <br>[ REFS: <i>result</i>, DEREFS: <i>none</i> ]
	 */
	public JDDNode getTransformedTransReward(JDDNode oldReward) throws PrismException
	{
		JDD.Ref(oldReward);
		return oldReward;
	}

	/**
	 * Get the transformed trans actions relation,
	 * mapping (state,action) to action index.
	 * <br>
	 * By default, the old trans action relation is returned.
	 * <br>[ REFS: <i>result</i>, DEREFS: <i>none</i> ]
	 */
	public JDDNode getTransformedTransActions() throws PrismException
	{
		if (originalModel.getTransActions() == null)
			return null;
		return originalModel.getTransActions().copy();
	}

	/**
	 * Directly provide the set of reachable states in the transformed model (optional).
	 * If the set of reachable states is not known, this function returns {@code null}
	 * and normal reachability computations will be performed.
	 * <br/>
	 * Default implementation: return {@code null}.
	 * <br/>
	 * [ REFS: <i>result</i> ]
	 */
	public JDDNode getReachableStates() throws PrismException {
		return null;
	}

	/**
	 * Provide a set of states in the transformed model that is known to be reachable
	 * for using as a seed in the subsequent reachability computation (speed-up).
	 * If this transformation does not want to provide this information,
	 * this function returns {@code null} and normal reachability computations
	 * will be performed (from the start states).
	 * <br/>
	 * Default implementation: return {@code null}
	 * [ REFS: <i>result</i> ]
	 */
	public JDDNode getReachableStateSeed() throws PrismException {
		return null;
	}

}
