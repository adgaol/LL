/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package DescendantLL;
import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Set;

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
    private Integer[][] table;
    private ArrayList<String> terminals;
    private ArrayList<String> noTerminals;
    public LL( String path) {
        this.grammar = new HashMap<>();
        this.grammarWithActions = new HashMap<>();
        this.path=path;
        readFile();
        grammarWithoutActions();
        this.head =  new HashMap<>();
        this.headPrime =  new HashMap<>();
        this.nexts =  new HashMap<>();
        this.directors =  new HashMap<>();
        this.terminals= new ArrayList<>();
        this.noTerminals=new ArrayList<>();
        noTerminals.addAll(grammar.keySet());
        this.table= new Integer[this.noTerminals.size()][this.terminals.size()];
        heads();
        nexts();
        directors();
        System.out.println("ce finit");
    }
    /**
     * Produce a new grammar without semantics actions
     */
    private void grammarWithoutActions(){
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
    private String removeActions(String production){
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
                        
                        String[] antecedentProducctios=line.split("::=");
                        if(contador==0)
                            axioma=antecedentProducctios[0];
                        String[] productions=antecedentProducctios[1].split("\\|");
                        ArrayList<String> productionsList = new ArrayList<>();
                        grammarWithActions.put(antecedentProducctios[0], productionsList);
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
    public ArrayList<String> directorAux(String production,String antecedent){
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
    private void ifNoRepeatInsert(ArrayList<String> oldElements,ArrayList<String> newElements ){
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
    private boolean containLambda(String symbol) {
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
    private boolean containLambda(ArrayList<String> symbols) {
        
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
   
}
