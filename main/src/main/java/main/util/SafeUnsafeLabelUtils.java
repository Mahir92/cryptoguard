package main.util;

import java.util.Map;
import java.util.Queue;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

public class SafeUnsafeLabelUtils {
    public static final String LINE_SEPERATOR = "< /br>";
    private static final String PART_SEPERATOR = " = ";

    private static Map<String, String> mpMethodCode;

    /**
     * Saves code snippet for the passed method signature
     * 
     * @param method
     * @param codeStr
     */
    public static void saveMethod(String method, String codeStr) {
        if (mpMethodCode == null)
            mpMethodCode = new HashMap<String, String>();

        mpMethodCode.put(method, codeStr);
    }

    /**
     * Checks if a method is unsafe (Currently based on only rule of returning
     * tainted variable)
     * 
     * @param methodSignature
     * @param reason
     * @return
     */
    public static boolean IsUnsafe(String methodSignature, String reason) {
        boolean isUnsafe = false;

        String method = getMethod(methodSignature);

        String taintedVariable = getTaintedVariable(method, reason);

        if (!taintedVariable.isEmpty()) {
            Map<String, List<String>> graph = prepareGraph(method);

            boolean isReturnValueTainted = isReturnValueTainted(graph, taintedVariable, method);

            // More rules will be introduced later
            if (isReturnValueTainted) {
                isUnsafe = true;
            }

        } else {
            System.err.println("Tainted variable not found");
        }

        return isUnsafe;
    }

    /**
     * Converts a method-code snippet to graph. Variable are the vertices of the
     * graph . There is an edge between two vertices if one impact another.
     * 
     * @param method
     * @return
     */
    private static Map<String, List<String>> prepareGraph(String method) {
        Map<String, List<String>> graph = new HashMap<String, List<String>>();

        String[] statements = method.split(LINE_SEPERATOR);
        List<String> vertices = new ArrayList<String>();

        // Finding the vertices
        for (String statement : statements) {
            String[] parts = statement.split(PART_SEPERATOR);

            // parts[0] = "$variable", parts[1] = INVOCATION/ASSIGNMENT;
            if (parts.length > 1) {
                vertices.add(parts[0]);
                graph.put(parts[0], new ArrayList<String>()); // Initializing edge list for the vertices
            }
        }

        // Preparing neighbor list for the vertices prepared before
        for (String statement : statements) {
            String[] parts = statement.split(PART_SEPERATOR);

            if (parts.length > 1) {
                for (String vertex : vertices) {
                    if (parts[1].contains(vertex)) {
                        graph.get(vertex).add(parts[0]); // adding the parts[0] as neighbors variables that has impact
                    }
                }
            }
        }

        return graph;
    }

    /**
     * Gets the tainted variable from code
     * 
     * @param method
     * @param vulnerableMethod
     * @return
     */
    private static String getTaintedVariable(String method, String vulnerableMethod) {
        String taintedVariable = "";

        String[] statements = method.split(LINE_SEPERATOR);
        for (String statement : statements) {
            String[] parts = statement.split(" = ");

            // parts[0] = "$variable", parts[1] = INVOCATION/ASSIGNMENT;
            if (parts.length > 1) {
                if (parts[1].contains(vulnerableMethod)) {
                    taintedVariable = parts[0];
                    break;
                }
            }
        }

        return taintedVariable;
    }

    /**
     * Checks if return value is impacted by tainted variable
     * 
     * @param graph
     * @param taintedVariable
     * @param method
     * @return
     */
    private static boolean isReturnValueTainted(Map<String, List<String>> graph, String taintedVariable,
            String method) {
        boolean isTainted = false;

        List<String> returnStatements = new ArrayList<String>();
        String[] statements = method.split(LINE_SEPERATOR);
        for (String statement : statements) {
            if (statement.startsWith("return")) {
                returnStatements.add(statement);
            }
        }

        List<String> taintedConnectedVariables = new ArrayList<String>();
        taintedConnectedVariables.add(taintedVariable);

        Queue<String> q = new LinkedList<String>();
        q.add(taintedVariable);
        Map<String, Boolean> visited = new HashMap<String, Boolean>();
        visited.put(taintedVariable, true);

        while (!q.isEmpty()) {
            String u = q.remove();
            for (String returnStatement : returnStatements) {
                if (returnStatement.contains(u)) {
                    System.out.println("Return statement: " + returnStatement + " tainted for: " + u);
                    isTainted = true;
                    break;
                }
            }
            if (isTainted)
                break;

            List<String> neighbors = graph.get(u);
            if (neighbors == null || neighbors.size() == 0) {
                // System.out.println("No neighbors");
                continue;
            }
            for (String v : neighbors) {
                if (visited.containsKey(v) && visited.get(v))
                    continue;
                visited.put(v, true);
                q.add(v); // In future, we can keep track of parent or distance from here
            }
        }

        return isTainted;
    }

    /**
     * Returns saved code snippet for method signature
     * 
     * @param method
     * @return
     */
    private static String getMethod(String method) {
        if (mpMethodCode.containsKey(method))
            return mpMethodCode.get(method);
        return "";
    }
}