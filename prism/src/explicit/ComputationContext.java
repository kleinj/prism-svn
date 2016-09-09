//==============================================================================
//	
//	Copyright (c) 2016-
//	Authors:
//	* Dave Parker <d.a.parker@cs.bham.ac.uk> (University of Birmingham/Oxford)
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

import param.BigRational;
import parser.ast.RelOp;

/**
 * Computation context for a model checking computation.
 * <br>
 * The information in the context is optional, but may serve
 * to improve the precision of the result (e.g., via graph-based
 * algorithms for qualitative properties) or to speed-up
 * the computation (e.g., by starting product constructions
 * only for the set of states of interest instead of all states).
 * <br>
 * By default, or in absence of a computation context,
 * the model checking algorithms should compute results for
 * all reachable states of the model.
 * <br>
 * In the presence of a computation context, the following
 * optimisations are allowed:
 * <ul>
 * <li>If {@code getStatesOfInterest() != null} then it suffices
 *     to compute results for the states with an index that is
 *     contained in the BitSet returned by
 *     {@code getStatesOfInterest()}. For other states, the
 *     result can be an arbitrary value (e.g., 0.0).
 * <li>If {@code isQualitative() == true} then it suffices to
 *     do perform a qualitative computation, i.e, all states
 *     with value 0 get result 0, all states with
 *     value 1 get result 1 and all other states get
 *     a result &gt;0 and &lt;1. By custom, for those states
 *     often 0.5 is returned.
 * <li>If {@code hasThreshold() == true} then it suffices
 *     that the result for a state satisfies the threshold
 *     if and only if the actual value for a state satisfies
 *     the threshold (as defined by {@code getThresholdOp()} and
 *     {@code getThresholdValue()}). As an example,
 *     for a threshold &gt;=0.5, a value iteration algorithm
 *     could return early if, for all states of interest, the computed
 *     value is larger than 0.5, even though the "exact" value
 *     is not yet known.
 * </ul>
 */
public class ComputationContext
{
	/** The states of interest. {@code null} = all reachable states of the model */
	private BitSet statesOfInterest = null;

	/** Is this a qualitative computation? */
	private boolean qualitative = false;

	/** The threshold operator, {@code null} = no threshold */
	private RelOp thresholdOp = null;

	/** The threshold value, {@code null} = no threshold */
	private Number threshold = null;

	/** Constructor, default values */
	public ComputationContext()
	{
	}

	/** Constructor, set the states of interest ({@code null} = all reachable states) */
	public ComputationContext(BitSet statesOfInterest)
	{
		this.statesOfInterest = statesOfInterest;
	}

	/**
	 * Get the states of interest for this context.
	 * A value of {@code null} signifies "all reachable state". 
	 */
	public BitSet getStatesOfInterest()
	{
		return statesOfInterest;
	}

	/**
	 * Set the flag for qualitative computation to {@code value}. 
	 */
	public void setQualitative(boolean value)
	{
		qualitative = value;
	}

	/** Is this a qualitative computation? */
	public boolean isQualitative()
	{
		return qualitative;
	}

	/**
	 * Does this context haves a threshold?
	 */
	public boolean hasThreshold()
	{
		return thresholdOp != null && threshold != null;
	}

	/**
	 * Set the threshold. If the threshold value is either 0 or 1, sets the 'qualitative' flag as well.
	 * @param thresholdOp the operator
	 * @param threshold the threshold (generally, either a Double or a BigRational)
	 */
	public void setThreshold(RelOp thresholdOp, Number threshold)
	{
		this.thresholdOp = thresholdOp;
		this.threshold = threshold;
		
		if (threshold instanceof Double) {
			if (threshold.doubleValue() == 0.0 ||
			    threshold.doubleValue() == 1.0) {
				setQualitative(true);
			}
		} else if (threshold instanceof BigRational) {
			BigRational thresholdRational = (BigRational) threshold;
			if (thresholdRational.equals(BigRational.ZERO) ||
				thresholdRational.equals(BigRational.ONE)) {
				setQualitative(true);
			}
		}

	}

	/** Remove a threshold from this context, if it exists */
	public void clearThreshold()
	{
		thresholdOp = null;
		threshold = null;
	}

	/**
	 * Get the threshold operator, {@code null} for "no threshold".
	 */
	public RelOp getThresholdOp()
	{
		return thresholdOp;
	}

	/**
	 * Get the threshold value, {@code null} for "no threshold".
	 * <br>
	 * This can be a Double or a BigRational.
	 */
	public Number getThreshold()
	{
		return threshold;
	}

	/**
	 * Returns a derived ComputationContext that only
	 * contains the information relevant for evaluating
	 * in a state formula context and stripping irrelevant
	 * information.
	 */
	ComputationContext toStateFormulaContext()
	{
		ComputationContext result = new ComputationContext();
		result.statesOfInterest = statesOfInterest;
		return result;
	}

	@Override
	public String toString()
	{
		String s = "";
		if (hasThreshold()) {
			s += "Threshold: " + getThresholdOp() + getThreshold();
		}
		if (isQualitative()) {
			if (!s.isEmpty())
				s +=", ";
			s += "Qualitative";
		}
		if (getStatesOfInterest() != null) {
			if (!s.isEmpty())
				s +=", ";
			s += "States of Interest = ";
			s += getStatesOfInterest();
		}

		return s;
	}
}
