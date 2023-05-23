/*
 * BSD 3-Clause License
 * 
 * Copyright (c) 2023, General Electric Company.
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * 1. Redistributions of source code must retain the above copyright notice, this
 *    list of conditions and the following disclaimer.
 * 
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 
 * 3. Neither the name of the copyright holder nor the names of its
 *    contributors may be used to endorse or promote products derived from
 *    this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package com.ge.oyster.translators;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.FuncInterp.Entry;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.apache.commons.math3.util.Pair;

// functions of this class is used to read the model returned by the SMT solver and return the
// information java data-structures (List, Map, etc.)
public class Z3ModelReader {

	// for a given datatype name and its constructor, it returns the actual constant
	// name

	public static FuncDecl<?> getZ3Constant(com.microsoft.z3.Model model, String constant) {
		for (FuncDecl<?> func : model.getConstDecls()) {
			if (func.getName().toString().equals(constant)) {
				return func;
			}
		}
		return null;
	}

	public static String getConstantName(com.microsoft.z3.Model model, String constructor, String dataType) {
		for (FuncDecl<?> func : model.getConstDecls()) {
			if (func.getRange().toString().equals(dataType)) {
				if (model.getConstInterp(func).getSExpr().equals(constructor)) {
					return func.getName().toString();
				}
			}
		}

		return null;
	}

	// this function returns the list of constructors (string) for a given datatype
	// name
	public static List<String> getConstructors(com.microsoft.z3.Model model, String datatype) {
		List<String> res = new ArrayList<String>();
		for (FuncDecl<?> func : model.getConstDecls()) {
			if (func.getRange().toString().equals(datatype)) {
				res.add(model.getConstInterp(func).getSExpr());
			}
		}

		return res;
	}

	// this function returns the list of constructors (smtlib expression) for a
	// given datatype name
	public static List<Expr> getConstructorsExpr(com.microsoft.z3.Model model, String datatype) {
		List<Expr> res = new ArrayList<Expr>();
		for (FuncDecl<?> func : model.getConstDecls()) {
			if (func.getRange().toString().equals(datatype)) {
				res.add(model.getConstInterp(func));
			}
		}

		return res;
	}

	// this functions creates a map from VL flow names to list of connections used
	// by the VL flow
	public static Map<String, List<String>> readFunc_VLFlow_Connection(com.microsoft.z3.Model model,
			com.microsoft.z3.Context ctx, Map<String, Pair<String, String>> flowNamesToSrcDestInstance) {
		Map<String, List<String>> resUnordered = new HashMap<String, List<String>>();
		Map<String, List<String>> resOrdered = new HashMap<String, List<String>>();
		Map<String, Pair<String, String>> connectionToPorts = func_Connection_Ports(model, ctx, "Port", "Connection",
				"Port");

		/*
		 * Map<String, List<String>> instanceToConnections =
		 * func_Instance_Connections(model, ctx, "Port", "Connection", "Port");
		 */

		// read the model to find all the connections used by a specific flow. The
		// connections are not in order here.
		for (FuncDecl<?> func : model.getFuncDecls()) {
			if (func.getName().toString().equals("VLFlow_Connection")) {
				List<Expr> vlflow_constructors = getConstructorsExpr(model, "VLFlow");
				List<Expr> connection_constructors = getConstructorsExpr(model, "Connection");
				for (Expr vlflow : vlflow_constructors) {
					String vlflowname = getConstantName(model, vlflow.getSExpr(), "VLFlow");
					for (Expr conn : connection_constructors) {
						String connectionname = getConstantName(model, conn.getSExpr(), "Connection");
						Expr eq = ctx.mkEq(func.apply(vlflow, conn), ctx.mkInt(1));
						Expr res = model.evaluate(eq, true);

						if (res.getSExpr().equals("true")) {
							List<String> elems = resUnordered.get(vlflowname);
							if (elems == null) {
								elems = new ArrayList<String>();
							}

						if(connectionToPorts.get(connectionname) != null) {		
							elems.add(connectionToPorts.get(connectionname).getFirst());
							elems.add(connectionname);
							elems.add(connectionToPorts.get(connectionname).getSecond());
						}
						
						if(connectionname.contains("ghost")) {
							List<String> endpoints = new ArrayList<>(Odm2Z3.ghostConnectionEndPoints.get(connectionname));
							elems.add(endpoints.get(0));
							elems.add(connectionname);
							elems.add(endpoints.get(1));
						}	
						
						resUnordered.put(vlflowname, elems);
						}
					}
				}
				break;
			}
			
		}

		// add ghost connections from resUnordered to connectionToPorts dictionary

		// now, we order the connections for a specific flows. We also add the two end
		// ports of each connection in the list
		// returns ordered ports and connections for a flow
		for (String newVlFlowName : resUnordered.keySet()) {
			// create ordered flows from the candidate flow segments
			List<String> flowElems = resUnordered.get(newVlFlowName);
			List flowElemsOrdered = new ArrayList();
			String srcIns = flowNamesToSrcDestInstance.get(newVlFlowName).getFirst();
			String destIns = flowNamesToSrcDestInstance.get(newVlFlowName).getSecond();
			String src = null;
			String dest = null;
			for (String ele : flowElems) {
				if (ele.contains(srcIns)) {
					src = ele;
				}
				if (ele.contains(destIns)) {
					dest = ele;
				}
			}
			// implement standard path finding algorithm while also using ghost connections
			String currentNode = src;
			while (currentNode != dest) {
				for (String con : connectionToPorts.keySet()) {
					if (flowElems.contains(con)) {
						if (connectionToPorts.get(con).getFirst().equals(currentNode)) {
							flowElemsOrdered.add(currentNode);
							if (!con.startsWith("ghost")) {
								flowElemsOrdered.add(con);
							}
							flowElemsOrdered.add(connectionToPorts.get(con).getSecond());
							currentNode = connectionToPorts.get(con).getSecond();
							continue;
						}

						if (connectionToPorts.get(con).getSecond().equals(currentNode)) {
							flowElemsOrdered.add(currentNode);
							if (!con.startsWith("ghost")) {
								flowElemsOrdered.add(con);
							}
							flowElemsOrdered.add(connectionToPorts.get(con).getFirst());
							currentNode = connectionToPorts.get(con).getFirst();
							continue;
						}
					}
				}
				for (String con : Odm2Z3.ghostConnectionEndPoints.keySet()) {
					if (flowElems.contains(con)) {
						if (Odm2Z3.ghostConnectionEndPoints.get(con).contains(currentNode)) {
							flowElemsOrdered.add(currentNode);
							String nextNode = null;
							for (String ele : Odm2Z3.ghostConnectionEndPoints.get(con)) {
								if (!ele.equals(currentNode)) {
									nextNode = ele;
									break;
								}
							}
							flowElemsOrdered.add(nextNode);
							currentNode = nextNode;
							continue;
						}

					}

				}

			}

			resOrdered.put(newVlFlowName, Z32AADL.removeDuplicates(flowElemsOrdered));

		}

		return resOrdered;
	}

	// reads the fixed-location-maps to find out sub-components of a component.
	// particularly, we check to which "rangeType" instance, the given "domainType"
	// instance is mapped
	public static Map<String, List<String>> readFunc_FLCmapping(com.microsoft.z3.Model model, String domainType,
			String rangeType) {
		Map<String, List<String>> res = new HashMap<String, List<String>>();
		List<String> constructors = getConstructors(model, domainType);
		for (FuncDecl<?> func : model.getFuncDecls()) {
			if (func.getName().toString().contains("_to_") && func.getDomain()[0].toString().equals(domainType)
					&& func.getRange().toString().equals(rangeType)) {
				Expr els = model.getFuncInterp(func).getElse();
				for (Entry<?> e : model.getFuncInterp(func).getEntries()) {
					String domain = domainType + "." + getConstantName(model, e.getArgs()[0].getSExpr(), domainType);
					String range = rangeType + "." + getConstantName(model, e.getValue().getSExpr(), rangeType);

					if (res.get(range) != null) {
						res.get(range).add(domain);
					} else {
						List<String> temp = new ArrayList<String>();
						temp.add(domain);
						res.put(range, temp);
					}

					constructors.remove(e.getArgs()[0].getSExpr());
				}

				if (els != null && constructors.size() > 0) {
					for (String con : constructors) {
						String domain = domainType + "." + getConstantName(model, con, domainType);
						String range = rangeType + "." + getConstantName(model, els.getSExpr(), rangeType);

						if (res.get(range) != null) {
							res.get(range).add(domain);
						} else {
							List<String> temp = new ArrayList<String>();
							temp.add(domain);
							res.put(range, temp);
						}
					}
				}
				break;
			}
		}

		return res;
	}

	public static Expr<?> eval(com.microsoft.z3.Model model, com.microsoft.z3.Context ctx, FuncDecl<?> func,
			String arg1, String arg2) {
		Expr<?> earg1 = ctx.mkConst(Z3ModelReader.getZ3Constant(model, arg1).getName(),
				Z3ModelReader.getZ3Constant(model, arg1).getRange());
		Expr<?> earg2 = ctx.mkConst(Z3ModelReader.getZ3Constant(model, arg2).getName(),
				Z3ModelReader.getZ3Constant(model, arg2).getRange());
		com.microsoft.z3.Expr<?>[] exprs = { earg1, earg2 };
		Expr<?> app = ctx.mkApp(func, exprs);
		Expr<?> result = model.eval(app, false);
		return result;
	}

	// reads the model to find mapping of a (port1, connection) pair to the other
	// end port (port2)
	public static Map<Pair<String, String>, String> readFunc_Port_Connection_Port(com.microsoft.z3.Model model,
			com.microsoft.z3.Context ctx, String domainType1, String domainType2, String rangeType) {
		Map<Pair<String, String>, String> res = new HashMap<Pair<String, String>, String>();
		List<String> constructors1 = getConstructors(model, domainType1);
		List<String> constructors2 = getConstructors(model, domainType2);
		/*
		 * for (FuncDecl<?> func : model.getFuncDecls()) { if
		 * (func.getName().toString().equals("Port_Connection_Port")) { Expr els =
		 * model.getFuncInterp(func).getElse(); for (Entry<?> e :
		 * model.getFuncInterp(func).getEntries()) { String domain1 =
		 * getConstantName(model, e.getArgs()[0].getSExpr(), domainType1); String
		 * domain2 = getConstantName(model, e.getArgs()[1].getSExpr(), domainType2);
		 * String range = getConstantName(model, e.getValue().getSExpr(), rangeType);
		 * res.put(new Pair(domain1, domain2), range);
		 * constructors1.remove(e.getArgs()[0].getSExpr());
		 * constructors1.remove(e.getValue().getSExpr());
		 * constructors2.remove(e.getArgs()[1].getSExpr()); }
		 * 
		 * constructors1.remove(els.getSExpr()); if (constructors1.size() == 1 &&
		 * constructors2.size() == 1) { String domain1 = getConstantName(model,
		 * constructors1.get(0), domainType1); String domain2 = getConstantName(model,
		 * constructors2.get(0), domainType2); String range = getConstantName(model,
		 * els.getSExpr(), rangeType); res.put(new Pair(domain1, domain2), range); }
		 * break; } }
		 */

		// evaluate the interpretation of Port_Connection_Port, add bi-directional edges

		FuncDecl<?> port_connection_func = null;
		for (FuncDecl<?> func : model.getFuncDecls()) {
			if (func.getName().toString().equals("Port_Connection_Port")) {
				port_connection_func = func;
				break;
			}
		}
		if (port_connection_func == null) {
			return res;
		}

		for (String conn : Odm2Z3.PortConnectionMap.keySet()) {
			String srcPort = Odm2Z3.PortConnectionMap.get(conn).sourceEntityName;
			Expr<?> destPortExpr = Z3ModelReader.eval(model, ctx, port_connection_func, srcPort, conn);
			String destPort = getConstantName(model, destPortExpr.getSExpr(), destPortExpr.getSort().toString());
			res.put(new Pair(srcPort, conn), destPort);
			// res.put(new Pair(destPort, conn), srcPort);
		}

		return res;
	}

	// reads the model to find mapping of a connection to the pair of ports
	public static Map<String, Pair<String, String>> func_Connection_Ports(com.microsoft.z3.Model model,
			com.microsoft.z3.Context ctx, String domainType1, String domainType2, String rangeType) {
		Map<String, Pair<String, String>> res = new HashMap<String, Pair<String, String>>();
		List<String> constructors1 = getConstructors(model, domainType1);
		List<String> constructors2 = getConstructors(model, domainType2);

		/*
		 * for (FuncDecl<?> func : model.getFuncDecls()) { if
		 * (func.getName().toString().equals("Port_Connection_Port")) { Expr els =
		 * model.getFuncInterp(func).getElse(); for (Entry<?> e :
		 * model.getFuncInterp(func).getEntries()) { String domain1 =
		 * getConstantName(model, e.getArgs()[0].getSExpr(), domainType1); String
		 * domain2 = getConstantName(model, e.getArgs()[1].getSExpr(), domainType2);
		 * String range = getConstantName(model, e.getValue().getSExpr(), rangeType);
		 * res.put(domain2, new Pair(domain1, range));
		 * constructors1.remove(e.getArgs()[0].getSExpr());
		 * constructors1.remove(e.getValue().getSExpr());
		 * constructors2.remove(e.getArgs()[1].getSExpr()); }
		 * 
		 * constructors1.remove(els.getSExpr()); if (constructors1.size() == 1 &&
		 * constructors2.size() == 1) { String domain1 = getConstantName(model,
		 * constructors1.get(0), domainType1); String domain2 = getConstantName(model,
		 * constructors2.get(0), domainType2); String range = getConstantName(model,
		 * els.getSExpr(), rangeType); res.put(domain2, new Pair(domain1, range)); }
		 * break; } }
		 */

		FuncDecl<?> port_connection_func = null;
		for (FuncDecl<?> func : model.getFuncDecls()) {
			if (func.getName().toString().equals("Port_Connection_Port")) {
				port_connection_func = func;
				break;
			}
		}
		if (port_connection_func == null) {
			return res;
		}

		for (String conn : Odm2Z3.PortConnectionMap.keySet()) {
			String srcPort = Odm2Z3.PortConnectionMap.get(conn).sourceEntityName;
			Expr<?> destPortExpr = Z3ModelReader.eval(model, ctx, port_connection_func, srcPort, conn);
			String destPort = getConstantName(model, destPortExpr.getSExpr(), destPortExpr.getSort().toString());
			res.put(conn, new Pair(srcPort, destPort));
			// res.put(new Pair(destPort, conn), srcPort);
		}

		return res;
	}

	// reads the model to find which connections are used by a component instance
	public static Map<String, List<String>> func_Instance_Connections(com.microsoft.z3.Model model,
			com.microsoft.z3.Context ctx, String domainType1, String domainType2, String rangeType) {
		Map<String, List<String>> res = new HashMap<String, List<String>>();
		List<String> constructors1 = getConstructors(model, domainType1);
		List<String> constructors2 = getConstructors(model, domainType2);
		for (FuncDecl<?> func : model.getFuncDecls()) {
			if (func.getName().toString().equals("Port_Connection_Port")) {
				/*
				 * Expr els = model.getFuncInterp(func).getElse(); for (Entry<?> e :
				 * model.getFuncInterp(func).getEntries()) { String domain1 =
				 * getConstantName(model, e.getArgs()[0].getSExpr(), domainType1)
				 * .split("\\.")[0]; String domain2 = getConstantName(model,
				 * e.getArgs()[1].getSExpr(), domainType2); String range =
				 * getConstantName(model, e.getValue().getSExpr(), rangeType) .split("\\.")[0];
				 * constructors1.remove(e.getArgs()[0].getSExpr());
				 * constructors1.remove(e.getValue().getSExpr());
				 * constructors2.remove(e.getArgs()[1].getSExpr());
				 * 
				 * if (res.get(domain1) != null) { res.get(domain1).add(domain2); } else {
				 * List<String> temp = new ArrayList<String>(); temp.add(domain2);
				 * res.put(domain1, temp); }
				 * 
				 * if (res.get(range) != null) { res.get(range).add(domain2); } else {
				 * List<String> temp = new ArrayList<String>(); temp.add(domain2);
				 * res.put(range, temp); } }
				 * 
				 * constructors1.remove(els.getSExpr()); if (constructors1.size() == 1 &&
				 * constructors2.size() == 1) { String domain1 = getConstantName(model,
				 * constructors1.get(0), domainType1) .split("\\.")[0]; String domain2 =
				 * getConstantName(model, constructors2.get(0), domainType2); String range =
				 * getConstantName(model, els.getSExpr(), rangeType).split("\\.")[0];
				 * 
				 * if (res.get(domain1) != null) { res.get(domain1).add(domain2); } else {
				 * List<String> temp = new ArrayList<String>(); temp.add(domain2);
				 * res.put(domain1, temp); }
				 * 
				 * if (res.get(range) != null) { res.get(range).add(domain2); } else {
				 * List<String> temp = new ArrayList<String>(); temp.add(domain2);
				 * res.put(range, temp); } } break;
				 */

				for (String conn : Odm2Z3.PortConnectionMap.keySet()) {
					String srcPort = Odm2Z3.PortConnectionMap.get(conn).sourceEntityName;
					Expr<?> destPortExpr = Z3ModelReader.eval(model, ctx, func, srcPort, conn);
					String destPort = getConstantName(model, destPortExpr.getSExpr(),
							destPortExpr.getSort().toString());

					String srcComp = srcPort.split("\\.")[0];
					String destComp = destPort.split("\\.")[0];
					// res.put(new Pair(destPort, conn), srcPort);
					List<String> srcConnList = res.get(srcComp);
					if (srcConnList == null) {
						srcConnList = new ArrayList<String>();
					}

					List<String> destConnList = res.get(destComp);
					if (destConnList == null) {
						destConnList = new ArrayList<String>();
					}

					if (!srcConnList.contains(conn)) {
						srcConnList.add(conn);
					}
					if (!destConnList.contains(conn)) {
						destConnList.add(conn);
					}

					res.put(srcComp, srcConnList);
					res.put(destComp, destConnList);
				}
			}
		}

		return res;
	}

	public static HashMap<String, HashMap<String, Integer>> readConst_ResourceUtilizations(
			com.microsoft.z3.Model model) {

		HashMap<String, HashMap<String, Integer>> resourceUtilization = new HashMap<>();
		List<String> oysterResourceProperties = Arrays.asList("cpuProvided", "cpuUsed", "ramProvided", "ramUsed",
				"romProvided", "romUsed");
		for (FuncDecl<?> func : model.getConstDecls()) {
			String constName = func.getName().toString();
			String property = getMatchingOysterResourceUtilizationProperty(constName);
			if (property != null) {
				int value = Integer.parseInt(model.getConstInterp(func).toString());
				String compName = constName.replace("_" + property, "");
				HashMap<String, Integer> map = resourceUtilization.get(compName);
				if (map == null) {
					map = new HashMap<String, Integer>();
				}
				map.put(property, value);
				resourceUtilization.put(compName, map);
			}
		}

		return resourceUtilization;
	}

	public static String getMatchingOysterResourceUtilizationProperty(String constName) {
		List<String> oysterResourceProperties = Arrays.asList("cpuProvided", "cpuUsed", "ramProvided", "ramUsed",
				"romProvided", "romUsed");
		for (String property : oysterResourceProperties) {
			if (constName.contains(property)) {
				return property;
			}
		}
		return null;
	}

	// returns a map from connection name to its bandwidth
	public static Map<String, Integer> readFunc_Connection_bandwidth(com.microsoft.z3.Model model, String domainType) {
		Map<String, Integer> res = new HashMap<String, Integer>();
		List<String> constructors = getConstructors(model, domainType);
		for (FuncDecl<?> func : model.getFuncDecls()) {
			if (func.getName().toString().equals("Connection_bandwidth")) {
				Expr els = model.getFuncInterp(func).getElse();
				for (Entry<?> e : model.getFuncInterp(func).getEntries()) {
					String domain = getConstantName(model, e.getArgs()[0].getSExpr(), domainType);
					Integer range = Integer.parseInt(e.getValue().getSExpr());
					res.put(domain, range);
					constructors.remove(e.getArgs()[0].getSExpr());
				}

				if (els != null && constructors.size() > 0) {
					for (String con : constructors) {
						String domain = getConstantName(model, con, domainType);
						Integer range = Integer.parseInt(els.getSExpr());
						res.put(domain, range);
					}
				}
				break;
			}
		}

		return res;
	}

	// returns a map from VL name to its MTU
	public static Map<String, Integer> getMap_VLToMtu(com.microsoft.z3.Model model) {
		Map<String, Integer> res = new HashMap<String, Integer>();
		for (FuncDecl<?> func : model.getConstDecls()) {
			if (func.getName().toString().endsWith("_mtu")) {
				Expr x = model.getConstInterp(func);
				res.put(func.getName().toString().split("_")[0], Integer.parseInt(x.getSExpr()));
			}
		}

		return res;
	}

	// returns a map from VL name to its Bag
	public static Map<String, Integer> getMap_VLToBag(com.microsoft.z3.Model model) {
		Map<String, Integer> res = new HashMap<String, Integer>();
		for (FuncDecl<?> func : model.getConstDecls()) {
			if (func.getName().toString().endsWith("_bag")) {
				Expr x = model.getConstInterp(func);
				res.put(func.getName().toString().split("_")[0], Integer.parseInt(x.getSExpr()));
			}
		}

		return res;
	}

	// returns the total network bandwidth computed by the solver
	public static Integer getNetBandwidth(com.microsoft.z3.Model model) {
		int res = -1;
		for (FuncDecl<?> func : model.getConstDecls()) {
			if (func.getName().toString().equals("NetworkBandwidthComputed")) {
				Expr x = model.getConstInterp(func);
				return Integer.parseInt(x.getSExpr());
			}
		}

		return res;
	}

	// returns a map from app name to its duration
	public static Map<String, Integer> getAppDurations(com.microsoft.z3.Model model) {
		Map<String, Integer> res = new HashMap<String, Integer>();
		for (FuncDecl<?> func : model.getConstDecls()) {
			if (func.getName().toString().endsWith("_duration")) {
				Expr x = model.getConstInterp(func);
				res.put(func.getName().toString().substring(0, func.getName().toString().length() - 9),
						Integer.parseInt(x.getSExpr()));
			}
		}

		return res;
	}

	// returns the period of the applications returned by the app scheduling
	// feature
	public static Map<Pair<String, String>, Integer> func_get_app_periods(com.microsoft.z3.Model model, Context ctx,
			List<String> instanceBoundTohostCompName) {
		// (app, proc) -> period
		Map<Pair<String, String>, Integer> res = new HashMap<Pair<String, String>, Integer>();

		for (FuncDecl<?> func : model.getFuncDecls()) {
			if (func.getName().toString().equals("App_periods_multi_core")) {
				List<Expr> app_constructors = getConstructorsExpr(model, "GPMApp");
				List<Expr> processor_constructors = getConstructorsExpr(model, "ProcessorGPM");
				for (Expr appExpr : app_constructors) {
					String app = getConstantName(model, appExpr.getSExpr(), "GPMApp");
					if (!instanceBoundTohostCompName.contains(app)) {
						continue;
					}

					for (Expr procExpr : processor_constructors) {
						String proc = getConstantName(model, procExpr.getSExpr(), "ProcessorGPM");
						if (!instanceBoundTohostCompName.contains(proc)) {
							continue;
						}

						int val = Integer.parseInt(model.evaluate(func.apply(appExpr, procExpr), true).toString());
						res.put(new Pair(app, proc), val);
					}
				}
			} else if (func.getName().toString().equals("App_periods_single_core")) {
				List<Expr> app_constructors = getConstructorsExpr(model, "GPMApp");
				for (Expr appExpr : app_constructors) {
					String app = getConstantName(model, appExpr.getSExpr(), "GPMApp");
					if (!instanceBoundTohostCompName.contains(app)) {
						continue;
					}

					int val = Integer.parseInt(model.evaluate(func.apply(appExpr), true).toString());
					res.put(new Pair(app, null), val);
				}
			}
		}

		return res;
	}

	// returns the info of the applications returned by the app scheduling
	// feature
	public static Map<String, AppScheduleInfo> func_get_app_start_times(com.microsoft.z3.Model model, Context ctx,
			List<String> instanceBoundTohostCompName) {
		// app -> (start_time, proc, duration, period)
		Map<String, AppScheduleInfo> res = new HashMap<String, AppScheduleInfo>();
		Map<String, Integer> app_durations = getAppDurations(model);
		Map<Pair<String, String>, Integer> app_periods = func_get_app_periods(model, ctx, instanceBoundTohostCompName);

		for (FuncDecl<?> func : model.getFuncDecls()) {
			if (func.getName().toString().equals("Multi_core_scheduling_map")) {
				List<Expr> app_constructors = getConstructorsExpr(model, "GPMApp");
				List<Expr> processor_constructors = getConstructorsExpr(model, "ProcessorGPM");
				for (Expr appExpr : app_constructors) {
					String app = getConstantName(model, appExpr.getSExpr(), "GPMApp");
					if (!instanceBoundTohostCompName.contains(app)) {
						continue;
					}

					for (Expr procExpr : processor_constructors) {
						String proc = getConstantName(model, procExpr.getSExpr(), "ProcessorGPM");
						if (!instanceBoundTohostCompName.contains(proc)) {
							continue;
						}

						int val = Integer.parseInt(model.evaluate(func.apply(appExpr, procExpr), true).toString());
						if (val >= 0) {
							res.put(app, new AppScheduleInfo(app, proc, app_durations.get(app),
									app_periods.get(new Pair(app, proc)), val, val));
						}
					}
				}
			} else if (func.getName().toString().equals("Single_core_scheduling_map")) {
				List<Expr> app_constructors = getConstructorsExpr(model, "GPMApp");
				for (Expr appExpr : app_constructors) {
					String app = getConstantName(model, appExpr.getSExpr(), "GPMApp");
					if (!instanceBoundTohostCompName.contains(app)) {
						continue;
					}

					int val = Integer.parseInt(model.evaluate(func.apply(appExpr), true).toString());
					if (val >= 0) {
						res.put(app, new AppScheduleInfo(app, null, app_durations.get(app),
								app_periods.get(new Pair(app, null)), val, val));
					}
				}
			}
		}

		return res;
	}

	// generates the schedule string based on the app start time, duration, period
	// we also compute and add the spare times here
	public static List<String> func_generate_schedule_strings(com.microsoft.z3.Model model,
			Map<String, AppScheduleInfo> appScheduleInfos) {
		List<String> finalres = new ArrayList<String>();
		Map<String, List<String>> proc_to_apps = new HashMap<String, List<String>>();
		Map<String, List<Integer>> proc_to_app_periods = new HashMap<String, List<Integer>>();
		List<Integer> app_periods = new ArrayList<Integer>();

		for (String app : appScheduleInfos.keySet()) {
			String proc = appScheduleInfos.get(app).procName;
			Integer app_period = appScheduleInfos.get(app).period;

			if (proc != null) { // multi-core
				if (proc_to_apps.get(proc) == null) {
					List<String> temp = new ArrayList<String>();
					List<Integer> temp2 = new ArrayList<Integer>();
					temp.add(app);
					temp2.add(app_period);
					proc_to_apps.put(proc, temp);
					proc_to_app_periods.put(proc, temp2);
				} else {
					proc_to_apps.get(proc).add(app);
					proc_to_app_periods.get(proc).add(app_period);
				}
			} else {
				// single core
				app_periods.add(app_period);
			}
		}

		// for multi-core
		if (proc_to_apps.keySet().size() > 0) {
			for (String proc : proc_to_apps.keySet()) {
				int majorTimeFrame = computeLCM(proc_to_app_periods.get(proc), 0);

				// add processor name, schedule ID and majorTimeFrame at the beginning
				// TODO: schedule ID = 1 is assumed for now. Need to make it flexible later
				String res = proc + " :1,";
				res = res + majorTimeFrame + "; ";

				// create a map from time to SPARE within majortimeFrame
				Map<Integer, String> timeToSpareMap = new HashMap<Integer, String>();
				int i = 0;
				int spare_count = 0;
				while (i < majorTimeFrame) {
					boolean found = false;
					for (String app : proc_to_apps.get(proc)) {
						int time = appScheduleInfos.get(app).start;
						if (time == i) {
							timeToSpareMap.put(i, app);

							if (spare_count > 0) {
								res = res + "SPARE" + "," + spare_count + "; ";
								spare_count = 0;
							}

							for (int j = 1; j < appScheduleInfos.get(app).duration; j++) {
								timeToSpareMap.put(i + j, app);
							}

							i = i + appScheduleInfos.get(app).duration - 1;
							appScheduleInfos.get(app).start = appScheduleInfos.get(app).start
									+ appScheduleInfos.get(app).period;
							res = res + app + "," + appScheduleInfos.get(app).duration + "; ";
							found = true;
							break;
						}
					}

					if (!(found)) {
						timeToSpareMap.put(i, "SPARE");
						spare_count++;
					}

					i++;
				}

				if (spare_count > 0) {
					res = res + "SPARE" + "," + spare_count + "; ";
				}

				finalres.add(res);
			}
		} else { // for single core
			int majorTimeFrame = computeLCM(app_periods, 0);

			// add schedule ID and majorTimeFrame at the beginning
			// TODO: schedule ID = 1 is assumed for now. Need to make it flexible later
			String res = "1,";
			res = res + majorTimeFrame + "; ";

			// create a map from time to SPARE within majortimeFrame
			Map<Integer, String> timeToSpareMap = new HashMap<Integer, String>();
			int i = 0;
			int spare_count = 0;
			while (i < majorTimeFrame) {
				boolean found = false;
				for (String app : appScheduleInfos.keySet()) {
					int time = appScheduleInfos.get(app).start;
					if (time == i) {
						timeToSpareMap.put(i, app);

						if (spare_count > 0) {
							res = res + "SPARE" + "," + spare_count + "; ";
							spare_count = 0;
						}

						for (int j = 1; j < appScheduleInfos.get(app).duration; j++) {
							timeToSpareMap.put(i + j, app);
						}

						i = i + appScheduleInfos.get(app).duration - 1;
						appScheduleInfos.get(app).start = appScheduleInfos.get(app).start
								+ appScheduleInfos.get(app).period;
						res = res + app + "," + appScheduleInfos.get(app).duration + "; ";
						found = true;
						break;
					}
				}

				if (!(found)) {
					timeToSpareMap.put(i, "SPARE");
					spare_count++;
				}

				i++;
			}

			if (spare_count > 0) {
				res = res + "SPARE" + "," + spare_count + "; ";
			}

			finalres.add(res);
		}

		return finalres;
	}

	// compute GCD of two numbers
	public static int GCD(int n1, int n2) {
		int gcd = 1;
		for (int i = 1; i <= n1 && i <= n2; ++i) {
			if (n1 % i == 0 && n2 % i == 0)
				gcd = i;
		}

		return gcd;
	}

	// compute LCM of list of numbers, recursively
	public static int computeLCM(List<Integer> values, int idx) {
		if (idx == values.size() - 1) {
			return values.get(idx);
		}

		int a = values.get(idx);
		int b = computeLCM(values, idx + 1);
		return (a * b / GCD(a, b));
	}
}