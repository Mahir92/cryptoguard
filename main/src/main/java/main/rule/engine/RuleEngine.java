package main.rule.engine;

import main.analyzer.backward.MethodWrapper;
import main.rule.*;
import main.util.*;
import soot.SootMethod;

import java.io.File;
import java.io.FileDescriptor;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Dictionary;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;

public class RuleEngine {
    private static List<RuleChecker> ruleCheckerList = new ArrayList<>();

    static {

        ruleCheckerList.add(new InsecureAssymCryptoFinder());
        ruleCheckerList.add(new BrokenCryptoFinder());
        ruleCheckerList.add(new UntrustedPrngFinder());
        ruleCheckerList.add(new SSLSocketFactoryFinder());
        ruleCheckerList.add(new CustomTrustManagerFinder());
        ruleCheckerList.add(new HostNameVerifierFinder());
        ruleCheckerList.add(new BrokenHashFinder());
        ruleCheckerList.add(new ConstantKeyFinder());
        ruleCheckerList.add(new PredictableIVFinder());
        ruleCheckerList.add(new PBESaltFinder());
        ruleCheckerList.add(new PBEInterationCountFinder());
        ruleCheckerList.add(new PredictableSeedFinder());
        ruleCheckerList.add(new PredictableKeyStorePasswordFinder());
        ruleCheckerList.add(new HttpUrlFinder());
    }

    public static void main(String[] args) throws Exception {

        // setting system output to a file
        System.setOut(new PrintStream(new File("./report.txt")));

        if (args.length < 2) {
            System.exit(1);
        }

        Utils.initDepth(Integer.parseInt(args[3]));

        if (args[0].equals("jar")) {
            String projectJarPath = args[1];
            String projectDependencyPath = args[2];

            System.out.println("Analyzing JAR: " + projectJarPath);

            for (RuleChecker ruleChecker : ruleCheckerList) {
                ruleChecker.checkRule(EngineType.JAR, Arrays.asList(projectJarPath),
                        Arrays.asList(projectDependencyPath));
            }

        } else if (args[0].equals("apk")) {
            String projectJarPath = args[1];

            System.out.println("Analyzing APK: " + projectJarPath);

            String basePackage = Utils.getBasePackageNameFromApk(projectJarPath);
            System.out.println("*** Base package: " + basePackage);

            for (RuleChecker ruleChecker : ruleCheckerList) {
                ruleChecker.checkRule(EngineType.APK, Arrays.asList(projectJarPath), null);
            }
        } else if (args[0].equals("source")) {

            String projectRoot = args[1];
            String projectDependencyPath = args[2];

            System.out.println("Analyzing Project: " + projectRoot);

            BuildFileParser buildFileParser = BuildFileParserFactory.getBuildfileParser(projectRoot);

            Map<String, List<String>> moduleVsDependency = buildFileParser.getDependencyList();

            List<String> analyzedModules = new ArrayList<>();

            for (String module : moduleVsDependency.keySet()) {

                if (!analyzedModules.contains(module)) {

                    String output = "Analyzing Module: ";

                    List<String> dependencies = moduleVsDependency.get(module);
                    List<String> otherdependencies = new ArrayList<>();

                    for (String dependency : dependencies) {

                        String dependencyModule = null;

                        if (dependency.equals(projectRoot + "/src/main/java")) {
                            dependencyModule = projectRoot.substring(projectRoot.lastIndexOf("/") + 1);
                            otherdependencies
                                    .add(dependency.substring(0, dependency.length() - 13) + projectDependencyPath);

                        } else {
                            dependencyModule = dependency.substring(projectRoot.length() + 1, dependency.length() - 14);
                            otherdependencies
                                    .add(dependency.substring(0, dependency.length() - 13) + projectDependencyPath);

                        }

                        output += dependencyModule + ", ";
                        analyzedModules.add(dependencyModule);
                    }

                    System.out.println(output.substring(0, output.length() - 2));

                    for (RuleChecker ruleChecker : ruleCheckerList) {
                        ruleChecker.checkRule(EngineType.SOURCE, dependencies, otherdependencies);
                    }

                    NamedMethodMap.clearCallerCalleeGraph();
                    FieldInitializationInstructionMap.reset();
                }
            }
        }

        // resetting system output to console
        System.setOut(new PrintStream(new FileOutputStream(FileDescriptor.out)));

        System.out.println("Total Heuristics: " + Utils.NUM_HEURISTIC);
        System.out.println("Total Orthogonal: " + Utils.NUM_ORTHOGONAL);
        System.out.println("Total Constants: " + Utils.NUM_CONSTS_TO_CHECK);
        System.out.println("Total Slices: " + Utils.NUM_SLICES);
        System.out.println("Average Length: " + RuleEngine.calculateAverage(Utils.SLICE_LENGTH));

        for (int i = 0; i < Utils.DEPTH_COUNT.length; i++) {
            System.out.println(String.format("Depth: %d, Count %d", i + 1, Utils.DEPTH_COUNT[i]));
        }

        VulnerabilityManager.getInstance().loadVulnerableMethods();
        generateCallGraph();
    }

    private static void generateCallGraph() throws IOException {
        List<String> vulnerableMethods = VulnerabilityManager.getInstance().getVulnerableMethods();
        StringBuilder sbReport = new StringBuilder();

        sbReport.append("Method\tAccess Modifier\tUnsafe");
        sbReport.append(System.lineSeparator());

        for (String method : vulnerableMethods) {
            Queue<String> qAffectedMethods = new LinkedList<>();
            qAffectedMethods.add(method);
            Dictionary<String, Integer> dictDistance = new Hashtable<>();
            dictDistance.put(method, 1);
            Dictionary<String, Boolean> dictColor = new Hashtable<>();
            dictColor.put(method, true);
            Dictionary<String, String> dictReason = new Hashtable<>();

            while (!qAffectedMethods.isEmpty()) {
                String currMethod = qAffectedMethods.peek();
                qAffectedMethods.remove();
                MethodWrapper methodWrapper = NamedMethodMap.getMethod(currMethod);

                if (methodWrapper != null) {
                    SootMethod sootMethod = methodWrapper.getMethod();

                    String accessModifier = "DEFAULT";
                    if (sootMethod.isPublic())
                        accessModifier = "PUBLIC";
                    if (sootMethod.isPrivate())
                        accessModifier = "PRIVATE";
                    else if (sootMethod.isProtected())
                        accessModifier = "PROTECTED";
                        
                    int currDist = dictDistance.get(currMethod);
                    String reason = dictReason.get(currMethod);

                    String unsafe;

                    if(reason == null) {
                        reason = "ACTUAL REASON";
                        unsafe = "Yes";
                    }
                    else {
                        unsafe = SafeUnsafeLabelUtils.IsUnsafe(currMethod, reason) ? "Yes" : "No";
                    }

                    //For keeping only the PUBLIC UNSAFE methods for now
                    
                    if(accessModifier.equals("PUBLIC") && unsafe.equals("Yes")) {
                        sbReport.append(
                                "\"" + currMethod + "\"\t" + accessModifier + "\t" + unsafe);
                        sbReport.append(System.lineSeparator());
                    }

                    for (MethodWrapper caller : methodWrapper.getCallerList()) {
                        SootMethod sootCallerMethod = caller.getMethod();
                        String callerMethod = sootCallerMethod.getSignature();

                        // System.out.println(callerMethod);

                        int dist;

                        try {
                            dist = dictDistance.get(callerMethod);
                        } catch (Exception ex) {
                            dist = 0;
                        }
                        if (dist == 0 || dist > currDist + 1) {
                            dist = currDist + 1;
                            dictDistance.put(callerMethod, dist);
                            qAffectedMethods.add(callerMethod);
                            dictReason.put(callerMethod, currMethod);
                        }
                    }
                }
            }

            // sbReport.append(new String(new char[40 + method.length() - 1]).replace("\0",
            // "*"));
            sbReport.append(System.lineSeparator());
        }

        FileWriter fw = new FileWriter("./output.txt");
        fw.write(sbReport.toString());
        fw.close();
    }

    private static double calculateAverage(List<Integer> marks) {
        Integer sum = 0;
        if (!marks.isEmpty()) {
            for (Integer mark : marks) {
                sum += mark;
            }
            return sum.doubleValue() / marks.size();
        }
        return sum;
    }
}
