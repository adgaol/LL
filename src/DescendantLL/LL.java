/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package DescendantLL;
import com.sun.xml.internal.ws.util.StringUtils;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Set;
import java.util.Stack;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import org.w3c.dom.Attr;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
/**
 *
 * @author adgao
 */
public class LL {
    private HashMap<String, ArrayList<String>> grammarWithActions;//antecedente, producciones// the grammar with the semantics actions
    private HashMap<String, ArrayList<String>> grammar;//antecedente, producciones//the grammar without the semantics actions
    private String path;//path of the file of the grammar
    private HashMap<String,ArrayList<String>> head;//antecedente, elementos de la cabecera//heads of every antecedent
    private HashMap<String,ArrayList<String>> headPrime;//antecedente, elementos de la cabecera//prime heads of every antecedent
    private HashMap<String,ArrayList<String>> nexts;// antecedentes , siguientes//nexts of every antecedent
    private HashMap<String,ArrayList<String>> directors; //producciones , directores//directors of every production
    private String axioma;//axioma of the grammar
    //private Integer[][] table;
    private HashMap<String,HashMap<String,Integer>> table;
    private HashMap<Integer,String>numRules;//indice, production
    private HashMap<String,Integer>indexRules;//production,indice
    private ArrayList<String> terminals;
    private ArrayList<String> noTerminals;
    private String entryChain;
    private HashMap<String, Double> values;
    private Document doc;
    private Integer ruleCount=1;
    private ArrayList<String> antecedentes;
    public LL( String path) {
        this.grammar = new HashMap<>();
        this.grammarWithActions = new HashMap<>();
        this.path=path;
        this.antecedentes=new ArrayList<>();
        readFile();
        grammarWithoutActions();
        this.head =  new HashMap<>();
        this.headPrime =  new HashMap<>();
        this.nexts =  new HashMap<>();
        this.directors =  new HashMap<>();
        this.terminals= new ArrayList<>();
        this.noTerminals=new ArrayList<>();
        noTerminals.addAll(grammar.keySet());
        this.table=new HashMap<>();
        this.numRules=new HashMap<>();
        this.indexRules=new HashMap<>();
        this.values=new HashMap<>();
        
        //this.table= new Integer[this.noTerminals.size()][this.terminals.size()];
        
        System.out.println("ce finit");
    }
    /**
     * build the processador
     */
    public void build(){
        heads();
        nexts();
        directors();
        indexingRules();
        poblationTable();
    }
    /**
     * Process the entry chain
     * @param entryChain 
     * chain to process
     */
    public void proccess(String entryChain){
        this.entryChain=entryChain;
        
        DocumentBuilderFactory dbFactory =DocumentBuilderFactory.newInstance();
        DocumentBuilder dBuilder=null;
        try {
            dBuilder = dbFactory.newDocumentBuilder();
        } catch (ParserConfigurationException ex) {
            Logger.getLogger(LL.class.getName()).log(Level.SEVERE, null, ex);
        }
        doc = dBuilder.newDocument();

        Element rootElement = doc.createElement("raiz");
        doc.appendChild(rootElement);
        Element espec = doc.createElement("espec");
        rootElement.appendChild(espec);
        Attr attr = doc.createAttribute("nombre");
	attr.setValue("Especificación del XML");
        espec.setAttributeNode(attr); 
        writeTraductor(espec);
        Stack<String> stack=new Stack<>();
        stack.push("$");
        stack.push(axioma);
        Stack<String> stackChain=new Stack<>();
        stackChain.push("$");
        //String[] chain=transformChain(entryChain).split(" ");
        String[] chain=entryChain.split(" ");
        for(int i=chain.length-1;i>=0;i--){
            stackChain.push(chain[i]);
        }
        while(!stack.isEmpty()){
            if(Character.isDigit(stackChain.peek().charAt(0))){
                Double value=Double.parseDouble(stackChain.pop());
                values.put("num.vlex", value);
                stackChain.push("num");
            }
            if(stack.peek().equals(stackChain.peek())){
                stack.pop();
                stackChain.pop();
            }
            else{
                if(!stack.peek().startsWith("{")){
                    
                    if(stack.peek().equals("λ")){
                        stack.pop();
                        
                    }
                    else{
                        if(!grammarWithActions.containsKey(stack.peek())){
                            String symbol=stack.pop();
                            Integer index=getNumberIndex(symbol);
                            stack.push(symbol.substring(0, index));
                        }
                        else{
                            Integer num=table.get(stack.pop()).get(stackChain.peek());
                            String production=numRules.get(num);
                            String[] symbols=production.split(" ");
                            
                            for(int i=symbols.length-1;i>0;i--){
                                stack.push(symbols[i]);
                            }
                        }
                    }
                }
                else{
                    String action=stack.pop();
                    
                    String[] varValue=action.substring(1,action.length()-2).split("=");
                    
                    Integer position=getNumberIndex(varValue[0].split("\\.")[0]);
                    
                    if(varValue.length>1){
                        if (position<varValue[0].split("\\.")[0].length()){
                            varValue[0]=varValue[0].split("\\.")[0].substring(0,position)+"."+varValue[0].split("\\.")[1];

                        }
                        position=getNumberIndex(varValue[1].split("\\.")[0]);
                        if (position<varValue[1].split("\\.")[0].length()){
                            varValue[1]=varValue[1].split("\\.")[0].substring(0,position)+"."+varValue[1].split("\\.")[1];

                        }
                        if(varValue[1].contains("+")||varValue[1].contains("-")||varValue[1].contains("/")||varValue[1].contains("*")){
                            Double value=calculateValue(varValue[1]);
                            values.put(varValue[0], value);
                        }

                        else{
                            values.put(varValue[0], values.get(varValue[1]));
                        }
                    }
                }
           }
       }
    TransformerFactory transformerFactory = TransformerFactory.newInstance();
    Transformer transformer=null;
        try {
            transformer = transformerFactory.newTransformer();
        } catch (TransformerConfigurationException ex) {
            Logger.getLogger(LL.class.getName()).log(Level.SEVERE, null, ex);
        }
    DOMSource source = new DOMSource(doc);
    StreamResult result = new StreamResult(new File("./cars.xml"));
        try {
            transformer.transform(source, result);
        } catch (TransformerException ex) {
            Logger.getLogger(LL.class.getName()).log(Level.SEVERE, null, ex);
        }

    // Output to console for testing
    StreamResult consoleResult = new StreamResult(System.out);
        try { 	
            transformer.transform(source, consoleResult);
        } catch (TransformerException ex) {
            Logger.getLogger(LL.class.getName()).log(Level.SEVERE, null, ex);
        }
    }
    /**
     * 
     * @param chain
     * @return 
     
    public String transformChain(String chain){
        String result="";
        String[] elements=chain.split(" ");
        for (int i=0;i<elements.length;i++){
            if(Character.isDigit(elements[i].charAt(0))){
                result+="num ";
            }
            else{
                result+=elements[i]+" ";
            }
        }
        return result.substring(0,result.length()-1);
    }*/
    /**
     * Produce a new grammar without semantics actions
     */
    public void grammarWithoutActions(){
        Set<String> antecedentes=grammarWithActions.keySet();
        for(String antecedent:antecedentes){
            ArrayList<String> productions=grammarWithActions.get(antecedent);
            ArrayList<String>newProductions=new ArrayList<>();
            for(String production:productions){
                String newProduction=removeActions(production);
                newProductions.add(newProduction);
            }
            grammar.put(antecedent, newProductions);
        }
    }
    /**
     * remove the semantics actions of a production
     * @param production
     * production where remove the semantics actions
     * @return
     * production without actions
     */
    public String removeActions(String production){
        String[] symbols=production.split(" ");
        String result="";
        for(int i=0;i<symbols.length;i++){
            String symbol=symbols[i];
            if(!symbol.startsWith("{")){
                if(grammarWithActions.containsKey(symbol)){
                    result+=symbol+" ";
                }
                else{
                    result+=symbol.substring(0, getNumberIndex(symbol))+" ";
                }
            }
        }
        return result.substring(0, result.length()-1);
    }
    /**
     * find the position where finnish the letters and begin the digits 
     * @param symbol
     * Symbol to find index
     * @return 
     * index of the symbol
     */
    private Integer getNumberIndex(String symbol){
        char[] letters=symbol.toCharArray();
        Integer index=letters.length;
        for(int i=0;i<letters.length;i++){
            if(Character.isDigit(letters[i])){
               index=i;
               return index;
            }
        }
        return index;
    }
    /**
     * read and save the grammar with actions semantics 
     */
    private void readFile() {
        try (BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(path), "UTF-16"))) { //mas-accesos-servidor-nitflex.log
	            String line;
                    int contador=0;
	            while ((line = br.readLine()) != null) {
                        
                        String[] antecedentProductions=line.split("::=");
                        if(contador==0)
                            axioma=antecedentProductions[0];
                        String[] productions=antecedentProductions[1].split("\\|");
                        if(!antecedentes.contains(antecedentProductions[0]))
                            antecedentes.add(antecedentProductions[0]);
                        ArrayList<String> productionsList = new ArrayList<>();
                        grammarWithActions.put(antecedentProductions[0], productionsList);
                        for(int i=0;i<productions.length;i++){
                            String production=productions[i];
                            productionsList.add(production);
                        }
                        contador++;
                    }
        }
        catch (IOException e) {
	    e.printStackTrace();
	}
    }
    /**
     * Calculate the directors
     */
    public void directors(){
          for(String antecedent:grammar.keySet()){
            for(String production:grammar.get(antecedent)){
                director(production,antecedent);
            }
        }
//        for(ArrayList<String> rule:grammar.values()){
//            for(String production:rule){
//                director(production);
//            }
//        }
    }
    /**
     * Calculate the director of one production
     * @param production
     * Production to calculate the director
     * @param antecedent 
     * Antecedent of the production
     */
    public void director(String production,String antecedent){
        String[] symbols=production.split(" ");
                ArrayList<String> directorsAux=new ArrayList<>();
                if(Character.isUpperCase(symbols[1].charAt(0))){
                    if(containLambda(head.get(symbols[1]))){
                        ifNoRepeatInsert(directorsAux,headPrime.get(symbols[1]));
                        ifNoRepeatInsert(directorsAux, directorAux(production.substring(1+symbols[1].length()),antecedent));
                    }
                    else{
                        ifNoRepeatInsert(directorsAux,head.get(symbols[1]));
                       
                    }
                }
                else if(symbols[1].equals("λ")){
                    ifNoRepeatInsert(directorsAux, nexts.get(antecedent));
                }
                else{
                    directorsAux.add(symbols[1]);
                }
                directors.put(antecedent+"::="+production, directorsAux);
    }
    /**
     * Calculate the director of one production
     * @param production
     * Production to calculate the director
     * @param antecedent 
     * Antecedent of the production
     * @return 
     * the directors of the production
     */
    private ArrayList<String> directorAux(String production,String antecedent){
        String[] symbols=production.split(" ");
                ArrayList<String> directorsAux=new ArrayList<>();
                if(Character.isUpperCase(symbols[1].charAt(0))){
                    if(containLambda(head.get(symbols[1]))){
                        ifNoRepeatInsert(directorsAux,headPrime.get(symbols[1]));
                        ifNoRepeatInsert(directorsAux, directorAux(production.substring(1+symbols[1].length()),antecedent));
                    }
                    else{
                        ifNoRepeatInsert(directorsAux,head.get(symbols[1]));
                       
                    }
                }
                else if(symbols[1].equals("λ")){
                   ifNoRepeatInsert(directorsAux, nexts.get(antecedent)); 
                }
                else{
                    directorsAux.add(symbols[1]);
                }
                return directorsAux;
    }
    /**
     * calculate all heads
     */
    public void heads(){
        for(String antecedent:grammar.keySet()){
            head(antecedent);
        }
    }
    /**
     * calculate one head
     * @param antecedent 
     * antecedent on which the head will be calculated
     */
    public void head(String antecedent){
        if(Character.isLowerCase(antecedent.charAt(0))){
            
        }
            //ArrayList<String> prueba=head.get(antecedent);
            if(head.get(antecedent)==null){
                ArrayList<String> productions=grammar.get(antecedent);
                ArrayList<String> aux=new ArrayList<>();
                for(String production:productions){
                    String first=production.substring(1, 2);
                    if(Character.isUpperCase(first.charAt(0))){
                        String[] consecuents =production.split(" ");
                        if(headPrime.get(consecuents[1])!=null)
                            aux.addAll(head.get(consecuents[0]));
                        else{
                            headPrime(consecuents[1]);
                            aux.addAll(headPrime.get(consecuents[1]));
                        }
                    }
                    else {
                        String[] consecuents =production.split(" ");
                        aux.add(consecuents[1]);
                    }
                }
                head.put(antecedent, aux);
            }
        
    }
    /**
     * calculate one  prime head 
     * @param antecedent 
     * antecedent on which the prime head will be calculated
     */
    public void headPrime(String antecedent){
        
        
            if(headPrime.get(antecedent)==null){
                ArrayList<String> productions=grammar.get(antecedent);
                ArrayList<String> aux=new ArrayList<>();
                for(String production:productions){
                    String first=production.substring(1, 2);
                    if(Character.isUpperCase(first.charAt(0))){
                        String[] consecuents =production.split(" ");
                        if(headPrime.get(consecuents[1])!=null)
                            aux.addAll(headPrime.get(consecuents[1]));
                        else
                            headPrime(consecuents[0]);
                    }
                    else if(first.charAt(0)!='λ'){
                        String[] consecuents =production.split(" ");
                        aux.add(consecuents[1]);
                    }
                    
                }  
                headPrime.put(antecedent, aux);
            }
          
    }
    /**
     * Calculate all the nexts
     */
    public void nexts(){
        for (String key:grammar.keySet()){
            next(key);
        }
    }
    /**
     * save the element in the list of next if is no repeat
     * @param oldElements
     * the elements in the list
     * @param newElements 
     * the elements to insert
     */
    public void ifNoRepeatInsert(ArrayList<String> oldElements,ArrayList<String> newElements ){
        for (String element: newElements){
            if(!oldElements.contains(element))
                oldElements.add(element);
        }
    }
    /**
     * Calculate one next
     * @param antecedente 
     * antecedent on which the next will be calculated
     */
    public void next(String antecedente){
        ArrayList<String> nextsForThis=new ArrayList<>();
        if(antecedente.equals(axioma)){           
            nextsForThis.add("$");
        }
        
        ArrayList<String> productionsWithElement= productionsWith(antecedente);

        for(String production:productionsWithElement){
            String[] symbols=production.split(" ");
            if(getIndex(symbols, antecedente)+1>=symbols.length){
                if(!getAntecedent(production).equals(antecedente))
                         if(nexts.get(getAntecedent(production))!=null)
                             ifNoRepeatInsert(nextsForThis,nexts.get(getAntecedent(production)));
//                             if(!nextsForThis.containsAll(nexts.get(getAntecedent(production))))
//                                nextsForThis.addAll(nexts.get(getAntecedent(production)));
                         else{
                             next(getAntecedent(production));
                             ifNoRepeatInsert(nextsForThis,nexts.get(getAntecedent(production)));
//                             if(!nextsForThis.containsAll(nexts.get(getAntecedent(production))))
//                                nextsForThis.addAll(nexts.get(getAntecedent(production)));
                         }
            }
            else if(Character.isUpperCase(symbols[getIndex(symbols, antecedente)+1].charAt(0))){
                Integer index=getIndex(symbols, antecedente)+1;
                if(headPrime.get(symbols[index])!=null)
                    ifNoRepeatInsert(nextsForThis,headPrime.get(symbols[index]));
//                    if(!nextsForThis.containsAll(headPrime.get(symbols[index])))
//                        nextsForThis.addAll(headPrime.get(symbols[index]));
                else{
                    headPrime(symbols[index]);
                    ifNoRepeatInsert(nextsForThis,headPrime.get(symbols[index]));
//                    if(!nextsForThis.containsAll(headPrime.get(symbols[index])))
//                        nextsForThis.addAll(headPrime.get(symbols[index]));
                }
                if(containLambda(symbols[index])&& index+1>=symbols.length){
                     if(!getAntecedent(production).equals(antecedente))
                         if(nexts.get(getAntecedent(production))!=null)
                             ifNoRepeatInsert(nextsForThis,nexts.get(getAntecedent(production)));
//                             if(!nextsForThis.containsAll(nexts.get(getAntecedent(production))))
//                                nextsForThis.addAll(nexts.get(getAntecedent(production)));
                         else{
                             next(getAntecedent(production));
                             ifNoRepeatInsert(nextsForThis,nexts.get(getAntecedent(production)));
//                             if(!nextsForThis.containsAll(nexts.get(getAntecedent(production))))
//                                nextsForThis.addAll(nexts.get(getAntecedent(production)));
                         }
                }
                else if(containLambda(symbols[index])){//&& getIndex(symbols, antecedente)+2<symbols.length){
                    if(Character.isUpperCase(symbols[index+1].charAt(0))){
                        next(symbols[index+1]);
                        ifNoRepeatInsert(nextsForThis,nexts.get(symbols[index+1]));
//                        if(!nextsForThis.containsAll(nexts.get(symbols[index+1])))
//                            nextsForThis.addAll(nexts.get(symbols[index+1]));
                    }
                    else{
//                        ifNoRepeatInsert(nextsForThis,nexts.get(symbols[index+1]));
                        if(!nextsForThis.contains(symbols[index+1]))
                        nextsForThis.add(symbols[index+1]);
                    }
                }

            }
            else{
                
                Integer index=getIndex(symbols, antecedente)+1;
                if(!nextsForThis.contains(symbols[index]))
                nextsForThis.add(symbols[index]);
                

                
            }
        }
        
        nexts.put(antecedente,nextsForThis);
    }
    /**
     * find all productions with the no terminal
     * @param noTerminal
     * no terminal to find
     * @return 
     * productions with the no terminal
     */
    public ArrayList<String> productionsWith(String noTerminal){
       ArrayList<String> result=new ArrayList<>();
       for (String key:grammar.keySet()){
           for(String production:grammar.get(key)){
               if(production.contains(noTerminal)){
                   result.add(production);
               }
           }
       } 
       return result;
    }
    /**
     * find the index where occur the element
     * @param production
     * production where find the element
     * @param element
     * element to find
     * @return 
     * index of the element
     */
    public Integer getIndex(String[] production, String element){
        int result=0;
        for(int i=0;i<production.length;i++){
            if(production[i].equals(element))
                result=i;
        }
        return result;
    }
    /**
     * check if the production of a symbol have lambda
     * @param symbol
     * symbol to check
     * @return 
     * true if have false if not
     */
    public boolean containLambda(String symbol) {
        ArrayList<String> productions=grammar.get(symbol);
        for(String production:productions){
            if(production.contains("λ")){
                return true;
            }
        }
        return false;
    }
    /**
     * Check if the list contains lambda
     * @param symbols
     * symbols to check
     * @return 
     * true if contains false if not
     */
    public boolean containLambda(ArrayList<String> symbols) {
        
        for(String symbol:symbols){
            if(symbol.equals("λ")){
                return true;
            }
        }
        return false;
    }
    /**
     * find the antecedent of the production
     * @param production
     * production to find the antecedente
     * @return 
     * the antecedent of the production
     */
    private String getAntecedent(String production){
        for(String key :grammar.keySet()){
            if (grammar.get(key).contains(production)){
                return key;
            }
        }
        return null;
    }
    /**
     * find all terminals and add them to a terminals atribute
     */
    private void groupTerminals(){
        for(ArrayList<String> productions:grammar.values()){
            for(String production:productions){
                String[] symbols=production.split(" ");
                for(int i=1;i<symbols.length;i++){
                    if(!Character.isUpperCase(symbols[i].charAt(0)))
                        terminals.add(symbols[i]);
                }
            }
        }
    }
   /**
    *poblate the table with the directors
    */
   public void poblationTable(){
       for(String rule:directors.keySet()){
           String production=rule.split("::=")[1];
           String antecedent=rule.split("::=")[0];
           HashMap<String,Integer> aux=new HashMap<>();
           for(String director:directors.get(rule)){
               if(table.get(antecedent)!=null)
                    table.get(antecedent).put(director, indexRules.get(rule));
               else{
                    aux.put(director, indexRules.get(rule));
                    table.put(antecedent, aux);
               }
           }
           
       }
       
   }
   /**
    *Build two maps, one with the index of the rule how key and production
    *how value, and other with production how key and index how value
    */
   private void indexingRules(){
       int i=0;
       for(String antecedente :grammarWithActions.keySet()){
           for(String production:grammarWithActions.get(antecedente)){
               numRules.put(i, production);
               String rule=removeActions(production);
               indexRules.put(antecedente+"::="+rule, i);
               i++;
           }
       }
   }
    /**
     * effectuate an aritmetic operation depending of the grammatical action
     * @param operation
     * operation to do(grammatical action)
     * @return 
     * the result of the operation
     */
    public Double calculateValue(String operation){
        Double result=0.0;
        
        if(operation.contains("+"))
            result=values.get(operation.split("\\+")[0])+values.get(operation.split("\\+")[1]);
        else if(operation.contains("-"))
            result=values.get(operation.split("-")[0])-values.get(operation.split("-")[1]);
        else if(operation.contains("*")){
            result=values.get(operation.split("\\*")[0])*values.get(operation.split("\\*")[1]);
        }
        else if(operation.contains("/"))
            result=values.get(operation.split("/")[0])/values.get(operation.split("/")[1]);
        return result;
    } 
    /**
     * write the part of tradutor and cadene in a xml
     * @param espec 
     * start of xml
     */
    private void writeTraductor(Element espec) {
        Element traductor = doc.createElement("traductor");
        espec.appendChild(traductor); 
        Element tipo= doc.createElement("tipo");
        traductor.appendChild(tipo);
        tipo.setTextContent("Descendente");
        for(String antecedent:antecedentes){
            for(String production:grammarWithActions.get(antecedent)){
              addRule(antecedent,production,traductor);  
            }
        }
        Element cadena = doc.createElement("cadena");
        espec.appendChild(cadena);
        cadena.setTextContent(entryChain);
    }
    /**
     * write a rule in xml
     * @param antecedent
     * antecendent of the rule
     * @param production
     * production of the antecedent to write
     * @param traductor 
     * element where to add the rule in the xml
     */
    private void addRule(String antecedent ,String production,Element traductor) {
        String id="R"+ruleCount;
        Element regla=doc.createElement("regla");
        traductor.appendChild(regla);
        Attr attrRegla = doc.createAttribute("id");
	attrRegla.setValue(id);
        regla.setAttributeNode(attrRegla);
        ArrayList<String> actions=actions(production);
        for(String action:actions){
            Element actionXml=doc.createElement("accionSemantica");
            regla.appendChild(actionXml);
            Integer pos=getPos(action,production);
            Attr attrAccion = doc.createAttribute("pos");
            attrAccion.setValue(pos.toString());
            actionXml.setAttributeNode(attrAccion);
            actionXml.setTextContent(action.substring(1,action.length()-1));
            if(pos<removeActions(production).split(" ").length){
                Element intermedio=doc.createElement("intermedio");
                actionXml.appendChild(intermedio);
                intermedio.setTextContent("si");
                
            }
            
        }
        addSymbols(production,regla,antecedent);
        ruleCount++;
    }
    /**
     * group the actions of one production
     * @param production
     * production where the actions are
     * @return 
     * A ArrayList with the actions
     */
    private ArrayList<String> actions(String production) {
        ArrayList<String> result=new ArrayList<>();
        String[] actions=production.split(" ");
        for(int i=1;i<actions.length;i++){
            if(actions[i].contains("{")){
                result.add(actions[i]);
            }
                
        }
        return result;
    }
    /**
     * obtain the position of the action in the production
     * @param action
     * action to find
     * @param production
     * production where find
     * @return 
     * the index of the symbol before the action
     */
    private Integer getPos(String action, String production) {
        Integer pos=0;
        int i=0;
        String[] symbols=production.split(" ");
        while(!symbols[i].equals(action)){
           
            if(!symbols[i].contains("{"))
                pos++;
            i++;
        }
        return pos;
    }
    /**
     * write the symbols of one rule in the xml
     * @param production
     * production where the symbols are
     * @param regla
     * element where to add the symbols in the xml
     * @param antecedente 
     * antecedent of the production
     */
    private void addSymbols(String production, Element regla,String antecedente) {
        String[] symbols=production.split(" ");
        for(int i=0;i<symbols.length;i++){
            if (i==0){
                 Element simbolo=doc.createElement("simbolo");
                regla.appendChild(simbolo);
                Element valor=doc.createElement("valor");
                simbolo.appendChild(valor);
                if(grammarWithActions.get(antecedente).get(0).equals(production))
                    valor.setTextContent(antecedente+"::=");
                else
                    valor.setTextContent("|");
                Element terminal=doc.createElement("terminal");
                simbolo.appendChild(terminal);
                
                terminal.setTextContent("false");
                
            }
            else if(!symbols[i].contains("{")){
                Element simbolo=doc.createElement("simbolo");
                regla.appendChild(simbolo);
                Element valor=doc.createElement("valor");
                simbolo.appendChild(valor);
                valor.setTextContent(symbols[i]);
                Element terminal=doc.createElement("terminal");
                simbolo.appendChild(terminal);
                if(Character.isUpperCase(symbols[i].charAt(0)))
                    terminal.setTextContent("false");
                else
                    terminal.setTextContent("true");
            }
        }
    }
}
