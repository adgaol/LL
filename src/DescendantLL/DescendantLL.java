/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package DescendantLL;

/**
 *
 * @author adgao
 */
public class DescendantLL {

    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) {
        if(args[0].equals("descendente")){
            LL ll= new LL(args[1]);
//            LL ll= new LL("Descendant.txt");
            ll.build();
            ll.proccess(args[2],args[3]);
            
//            ll.proccess("2 * 4 + 3 ;", "./"+"Descendant.xml");
        }
    }
    
}
