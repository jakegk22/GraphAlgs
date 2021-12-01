/*************************************************************************
*  An Airline management system that uses a weighted-edge directed graph 
*  implemented using adjacency lists.
*************************************************************************/
import java.util.*;

import java.io.*;

public class AirlineSystem {
  private String [] cityNames = null;
  private Digraph G = null;
  private Digraph costG = null;//added costG to hold costs as weights 
  private static Scanner scan = null;
  private static final int INFINITY = Integer.MAX_VALUE;


  /**
  * Test client.
  */
  public static void main(String[] args) throws IOException {
    AirlineSystem airline = new AirlineSystem();
    scan = new Scanner(System.in);
    while(true){
      switch(airline.menu()){
        case 1:
          airline.readGraph();
          break;
        case 2:
          airline.printGraph();
          airline.printMST();
          break;
        case 3:
          airline.shortestHops();
          break;
        case 4:
            airline.shortestDistance();
            break;
        case 5:
            airline.cheapestCost();
            break;
        case 6:
            airline.findLessThen();
            break;
        case 7:
            airline.addFlight();
            break;
        case 8:
            airline.removeFlight();
            break;                        
        case 9:
          scan.close();
          System.exit(0);
          break;
        default:
          System.out.println("Incorrect option.");
      }
    }
  }

  private int menu(){
    System.out.println("*********************************");
    System.out.println("Welcome to FifteenO'One Airlines!");
    System.out.println("1. Read data from a file.");
    System.out.println("2. Display all routes.");
    System.out.println("3. Compute shortest path based on number of hops.");
    System.out.println("4. Compute shortest path based on distance.");
    System.out.println("5. Compute shortest path based on price.");
    System.out.println("6. Compute paths that are less than or equal to a target price.");
    System.out.println("7. Add a new route to the schedule.");
    System.out.println("8. remove a route from the schedule.");
    System.out.println("9. Exit.");
    System.out.println("*********************************");
    System.out.print("Please choose a menu option (1-9): ");

    int choice = Integer.parseInt(scan.nextLine());
    return choice;
  }

  private void readGraph() throws IOException {
    System.out.println("Please enter graph filename:");
    String fileName = scan.nextLine();
    Scanner fileScan = new Scanner(new FileInputStream(fileName));
    int v = Integer.parseInt(fileScan.nextLine());
    G = new Digraph(v);
    costG = new Digraph(v); //create costG to hold costs as weights 

    cityNames = new String[v];
    for(int i=0; i<v; i++){
      cityNames[i] = fileScan.nextLine();
    }

    while(fileScan.hasNext()){
      int from = fileScan.nextInt();
      int to = fileScan.nextInt();
      int weight = fileScan.nextInt();
      double cost = fileScan.nextDouble();
      G.addEdge(new WeightedDirectedEdge(from-1, to-1, weight,cost));
      //G.addEdge(new WeightedDirectedEdge(to-1, from-1, weight,cost));
      costG.addEdge(new WeightedDirectedEdge(from-1, to-1, cost));
      //costG.addEdge(new WeightedDirectedEdge(to-1, from-1, cost));
      //fileScan.nextLine();   //this line fucked up program when reading in test files
    }
    fileScan.close();
    System.out.println("Data imported successfully.");
    System.out.print("Please press ENTER to continue ...");
    scan.nextLine();
  }

  private void printGraph() {
    if(G == null){
      System.out.println("Please import a graph first (option 1).");
      System.out.print("Please press ENTER to continue ...");
      scan.nextLine();
    } else {
      for (int i = 0; i < G.v; i++) {
        System.out.print(cityNames[i] + ": ");
        for (WeightedDirectedEdge e : G.adj(i)) {
          System.out.print(cityNames[e.to()] + "(" + e.weight() + ") $" + e.cost() + " ");
        }
        System.out.println();
      }
      System.out.print("Please press ENTER to continue ...");
      scan.nextLine();

    }
  }

  private void printMST(){
    PrimMST mst = new PrimMST(G);
    
    Iterable<WeightedDirectedEdge> edges = mst.edges();
    for(WeightedDirectedEdge e : edges){
      System.out.println(cityNames[e.from()] + " -> " + cityNames[e.to()] + " Miles: " + e.weight() + " cost: $" + e.cost() );
      System.out.println();
    }
  }

  private void shortestHops() {
    if(G == null){
      System.out.println("Please import a graph first (option 1).");
      System.out.print("Please press ENTER to continue ...");
      scan.nextLine();
    } else {
      for(int i=0; i<cityNames.length; i++){
        System.out.println(i+1 + ": " + cityNames[i]);
      }
      System.out.print("Please enter source city (1-" + cityNames.length + "): ");
      int source = Integer.parseInt(scan.nextLine());
      System.out.print("Please enter destination city (1-" + cityNames.length + "): ");
      int destination = Integer.parseInt(scan.nextLine());
      source--;
      destination--;
      G.bfs(source);
      if(!G.marked[destination]){
        System.out.println("There is no route from " + cityNames[source]
                            + " to " + cityNames[destination]);
      } else {
         // TODO: Use a stack to construct the shortest path from the edgeTo array
        // then print the shortest distance (from the distTo array) and the path
	    // with the weight of each edge (see example output)
        Stack<Integer> path = new Stack<>();
        for (int x = destination; x != source; x = G.edgeTo[x]){
            path.push(x);
        }
        System.out.print("The shortest route from " + cityNames[source] + " to " + cityNames[destination] + " has " +  G.distTo[destination] + " hops: ");

        //int prevVertex = source;
        //System.out.print(cityNames[source] + " ");
        while(!path.empty()){
          int v = path.pop();
          System.out.print( cityNames[v] + " ");
          //prevVertex = v;
        }
        System.out.println();
      }
      System.out.print("Please press ENTER to continue ...");
      scan.nextLine();
    }
  }

  private void shortestDistance(){
      if(G == null){
        System.out.println("Please import a graph first (option 1).");
        System.out.print("Please press ENTER to continue ...");
        scan.nextLine();
      } else {
        for(int i=0; i<cityNames.length; i++){
          System.out.println(i+1 + ": " + cityNames[i]);
        }
        System.out.print("Please enter source city (1-" + cityNames.length + "): ");
        int source = Integer.parseInt(scan.nextLine());
        System.out.print("Please enter destination city (1-" + cityNames.length + "): ");
        int destination = Integer.parseInt(scan.nextLine());
        source--;
        destination--;
        G.dijkstras(source, destination,true);
        if(!G.marked[destination]){
          System.out.println("There is no route from " + cityNames[source]
                              + " to " + cityNames[destination]);
        } else {
          Stack<Integer> path = new Stack<>();
          for (int x = destination; x != source; x = G.edgeTo[x]){
              path.push(x);
          }
          System.out.print("The shortest route from " + cityNames[source] +
                             " to " + cityNames[destination] + " has " +
                             G.distTo[destination] + " miles: ");

          int prevVertex = source;
          System.out.print(cityNames[source] + " ");
          while(!path.empty()){
            int v = path.pop();
            System.out.print(G.distTo[v] - G.distTo[prevVertex] + " "
                             + cityNames[v] + " ");
            prevVertex = v;
          }
          System.out.println();

        }
        System.out.print("Please press ENTER to continue ...");
        scan.nextLine();
      }


  }
  private void cheapestCost(){
    if(costG == null){
      System.out.println("Please import a graph first (option 1).");
      System.out.print("Please press ENTER to continue ...");
      scan.nextLine();
    }else{
      for(int i=0; i<cityNames.length; i++){
        System.out.println(i+1 + ": " + cityNames[i]);
      }
      System.out.print("Please enter source city (1-" + cityNames.length + "): ");
      int source = Integer.parseInt(scan.nextLine());
      System.out.print("Please enter destination city (1-" + cityNames.length + "): ");
      int destination = Integer.parseInt(scan.nextLine());
      source--;
      destination--;
      costG.dijkstras(source, destination,false);
      if(!costG.marked[destination]){
        System.out.println("There is no route from " + cityNames[source]
                            + " to " + cityNames[destination]);
      } else {
        Stack<Integer> path = new Stack<>();
        for (int x = destination; x != source; x = costG.edgeTo[x]){
            path.push(x);
        }
        System.out.print("The cheapest route from " + cityNames[source] +
                           " to " + cityNames[destination] + " is " +
                           costG.distTo[destination] + " dollars: ");

        int prevVertex = source;
        System.out.print(cityNames[source] + " ");
        while(!path.empty()){
          int v = path.pop();
          System.out.print((costG.distTo[v] - costG.distTo[prevVertex])+ " "
                           + cityNames[v] + " ");
          prevVertex = v;
        }
        System.out.println();

      }
      System.out.print("Please press ENTER to continue ...");
      scan.nextLine();     
    }
  }

  private void findLessThen(){
    System.out.println("Enter your max cost:");
    int max = scan.nextInt();
  }

  private void addFlight(){
    for(int i=0; i<cityNames.length; i++){
      System.out.println(i+1 + ": " + cityNames[i]);
    }
    System.out.print("Please enter source city (1-" + cityNames.length + "): ");
    int source = Integer.parseInt(scan.nextLine());
    System.out.print("Please enter destination city (1-" + cityNames.length + "): ");
    int destination = Integer.parseInt(scan.nextLine());
    source--;
    destination--;
    System.out.print("Enter distance of miles:");
    int miles = scan.nextInt();
    System.out.print("Enter cost of new flight:");
    double cost = scan.nextDouble();

    G.addEdge(new WeightedDirectedEdge(source, destination, miles,cost));
    costG.addEdge(new WeightedDirectedEdge(source, destination, cost));

    System.out.println();
    System.out.println("Route added:" + cityNames[source]+ " to " + cityNames[destination] + " miles:" + miles + " for $" + cost);
    System.out.println();

    System.out.print("Please press ENTER to continue ...");
    scan.nextLine();
  }  

  private void removeFlight(){
    for(int i=0; i<cityNames.length; i++){
      System.out.println(i+1 + ": " + cityNames[i]);
    }
    System.out.print("Please enter source city (1-" + cityNames.length + "): ");
    int source = Integer.parseInt(scan.nextLine());
    System.out.print("Please enter destination city (1-" + cityNames.length + "): ");
    int destination = Integer.parseInt(scan.nextLine());
    source--;
    destination--;
    G.removeEdge(source,destination);
  }
  /**
  *  The <tt>Digraph</tt> class represents an directed graph of vertices
  *  named 0 through v-1. It supports the following operations: add an edge to
  *  the graph, iterate over all of edges leaving a vertex.Self-loops are
  *  permitted.
  */
  private class Digraph {
    private final int v;
    private int e;
    private LinkedList<WeightedDirectedEdge>[] adj;
    private boolean[] marked;  // marked[v] = is there an s-v path
    private int[] edgeTo;      // edgeTo[v] = previous edge on shortest s-v path
    private int[] distTo;      // distTo[v] = number of edges shortest s-v path


    /**
    * Create an empty digraph with v vertices.
    */
    public Digraph(int v) {
      if (v < 0) throw new RuntimeException("Number of vertices must be nonnegative");
      this.v = v;
      this.e = 0;
      @SuppressWarnings("unchecked")
      LinkedList<WeightedDirectedEdge>[] temp =
      (LinkedList<WeightedDirectedEdge>[]) new LinkedList[v];
      adj = temp;
      for (int i = 0; i < v; i++)
        adj[i] = new LinkedList<WeightedDirectedEdge>();
    }

    /**
    * Add the edge e to this digraph.
    */
    public void addEdge(WeightedDirectedEdge edge) {
      int from = edge.from();
      adj[from].add(edge);
      e++;
    }

    public void removeEdge(int source, int destination){
      //int to = edge.to();
      adj[source].remove(destination);
      adj[destination].remove(source);
      e--;
    }


    /**
    * Return the edges leaving vertex v as an Iterable.
    * To iterate over the edges leaving vertex v, use foreach notation:
    * <tt>for (WeightedDirectedEdge e : graph.adj(v))</tt>.
    */
    public Iterable<WeightedDirectedEdge> adj(int v) {
      return adj[v];
    }

    public void bfs(int source) {
      marked = new boolean[this.v];
      distTo = new int[this.e];
      edgeTo = new int[this.v];

      Queue<Integer> q = new LinkedList<Integer>();
      for (int i = 0; i < v; i++){
        distTo[i] = INFINITY;
        marked[i] = false;
      }
      distTo[source] = 0;
      marked[source] = true;
      q.add(source);

      while (!q.isEmpty()) {
        int v = q.remove();
        for (WeightedDirectedEdge w : adj(v)) {
          if (!marked[w.to()]) {
            edgeTo[w.to()] = v;
            distTo[w.to()] = distTo[v] + 1;
            marked[w.to()] = true;
            q.add(w.to());
          }
        }
      }
    }

    public void dijkstras(int source, int destination, boolean dist) {
      marked = new boolean[this.v];
      distTo = new int[this.v];
      edgeTo = new int[this.v];


      for (int i = 0; i < v; i++){
        distTo[i] = INFINITY;
        marked[i] = false;
      }
      distTo[source] = 0;
      marked[source] = true;
      int nMarked = 1;

      int current = source;
      while (nMarked < this.v) {
        for (WeightedDirectedEdge w : adj(current)) {
          if(dist){
            if (distTo[current]+w.weight() < distTo[w.to()]) {
	            //TODO:update edgeTo and distTo
              distTo[w.to()] = distTo[current] + w.weight();
              edgeTo[w.to()] = current;
            }
          }
          else{
            if (distTo[current]+w.cost() < distTo[w.to()]) {
	            //TODO:update edgeTo and distTo
              edgeTo[w.to()] = current;
              distTo[w.to()] = (int) (distTo[current] + w.cost());
              
            }
          }
        }
        //Find the vertex with minimim path distance
        //This can be done more effiently using a priority queue!
        int min = INFINITY;
        current = -1;

        for(int i=0; i<distTo.length; i++){
          if(marked[i])
            continue;
          if(distTo[i] < min){
            min = distTo[i];
            current = i;
          }
        }

	//TODO: Update marked[] and nMarked. Check for disconnected graph.
        if(current == -1) break;
        if(current >= 0){
          marked[current] = true;
          nMarked++;
        }
      }
    }

    
  }

  /**
  *  The <tt>WeightedDirectedEdge</tt> class represents a weighted edge in an directed graph.
  */

  private class WeightedDirectedEdge implements Comparable<WeightedDirectedEdge>{
    private final int v;
    private final int w;
    private int weight;
    private double cost; //added a cost var for cost graph
    /**
    * Create a directed edge from v to w with given weight.
    */
    public WeightedDirectedEdge(int v, int w, int weight,double cost) {
      this.v = v;
      this.w = w;
      this.weight = weight;
      this.cost = cost;
    }

    public WeightedDirectedEdge(int v, int w, double cost){ //new constructor to make a cost graph using double as an arg
      this.v = v;
      this.w = w;
      this.cost = cost;
    }
    public int from(){
      return v;
    }

    public int to(){
      return w;
    }

    public int weight(){
      return weight;
    }

    public double cost(){
      return cost;
    }

    @Override
    public int compareTo(WeightedDirectedEdge o) {
      // TODO Auto-generated method stub
      if(this.weight() == ((AirlineSystem.WeightedDirectedEdge) o).weight())
        return 0;
      else if(this.weight > ((AirlineSystem.WeightedDirectedEdge) o).weight())
        return 1;
      else return -1;
    }
  }


  private class PrimMST {
    private static final double FLOATING_POINT_EPSILON = 1E-12;

    private WeightedDirectedEdge[] edgeTo;        // edgeTo[v] = shortest edge from tree vertex to non-tree vertex
    private int[] distTo;      // distTo[v] = weight of shortest such edge
    private boolean[] marked;     // marked[v] = true if v on tree, false otherwise
    private PriorityQueue<Integer> pq;

    /**
     * Compute a minimum spanning tree (or forest) of an edge-weighted graph.
     * @param G the edge-weighted graph
     */
    public PrimMST(Digraph G) {
        edgeTo = new WeightedDirectedEdge[G.v];
        distTo = new int[G.v];
        marked = new boolean[G.v];
        pq = new PriorityQueue<Integer>(G.v);
        for (int v = 0; v < G.v; v++)
            distTo[v] = Integer.MAX_VALUE;

        for (int v = 0; v < G.v; v++)      // run from each vertex to find
            if (!marked[v]) prim(G, v);      // minimum spanning forest

        // check optimality conditions
        assert check(G);
    }

    // run Prim's algorithm in graph G, starting from vertex s
    private void prim(Digraph G, int s) {
        distTo[s] = 0;
        pq.add(distTo[s]);
        while (!pq.isEmpty()) {
            int v = pq.poll();
            scan(G, v);
        }
    }
    

    // scan vertex v
    private void scan(Digraph G, int v) {
        marked[v] = true;
        for (WeightedDirectedEdge e : G.adj(v)) {
            int w = e.to();
            if (marked[w]) continue;         // v-w is obsolete edge
            if (e.weight() < distTo[w]) {
                distTo[w] = e.weight();
                edgeTo[w] = e;
                if (pq.contains(w)) pq.remove(w);
                else                pq.add(w);
            }
            
        }
    }

    /**
     * Returns the edges in a minimum spanning tree (or forest).
     * @return the edges in a minimum spanning tree (or forest) as
     *    an iterable of edges
     */
    public Iterable<WeightedDirectedEdge> edges() {
        Queue<WeightedDirectedEdge> mst = new LinkedList<WeightedDirectedEdge>();

        for (int v = 0; v < edgeTo.length; v++) {
            WeightedDirectedEdge e = edgeTo[v];
            if (e != null) {
                mst.add(e);
            }
        }
        return mst;
    }

    /**
     * Returns the sum of the edge weights in a minimum spanning tree (or forest).
     * @return the sum of the edge weights in a minimum spanning tree (or forest)
     */
    public double weight() {
        double weight = 0.0;
        for (WeightedDirectedEdge e : edges())
            weight += e.weight();
        return weight;
    }


    // check optimality conditions (takes time proportional to E V lg* V)
    private boolean check(Digraph G) {

        // check weight
        double totalWeight = 0.0;
        for (WeightedDirectedEdge e : edges()) {
            totalWeight += e.weight();
        }
        if (Math.abs(totalWeight - weight()) > FLOATING_POINT_EPSILON) {
            System.err.printf("Weight of edges does not equal weight(): %f vs. %f\n", totalWeight, weight());
            return false;
        }

        // check that it is acyclic
        UF uf = new UF(G.v);
        for (WeightedDirectedEdge e : edges()) {
            int v = e.to(), w = e.from();
            if (uf.find(v) == uf.find(w)) {
                System.err.println("Not a forest");
                return false;
            }
            uf.union(v, w);
        }

        // check that it is a spanning forest
        int i =0;
        for (WeightedDirectedEdge e : G.adj(i)) {
            int v = e.to(), w = e.from();
            if (uf.find(v) != uf.find(w)) {
                System.err.println("Not a spanning forest");
                return false;
            }
            i++;
        }

        // check that it is a minimal spanning forest (cut optimality conditions)
        for (WeightedDirectedEdge e : edges()) {

            // all edges in MST except e
            uf = new UF(G.v);
            for (WeightedDirectedEdge f : edges()) {
                int x = f.to(), y = f.from();
                if (f != e) uf.union(x, y);
            }

            // check that e is min weight edge in crossing cut
            i=0;
            for (WeightedDirectedEdge f : G.adj(i)) {
                int x = f.from(), y = f.to();
                if (uf.find(x) != uf.find(y)) {
                    if (f.weight() < e.weight()) {
                        System.err.println("Edge " + f + " violates cut optimality conditions");
                        return false;
                    }
                }
                i++;
            }

        }

        return true;
    }

    /**
     * Unit tests the {@code PrimMST} data type.
     *
     * @param args the command-line arguments
     */



}

  public class UF {

    private int[] parent;  // parent[i] = parent of i
    private byte[] rank;   // rank[i] = rank of subtree rooted at i (never more than 31)
    private int count;     // number of components

    /**
     * Initializes an empty union-find data structure with
     * {@code n} elements {@code 0} through {@code n-1}.
     * Initially, each elements is in its own set.
     *
     * @param  n the number of elements
     * @throws IllegalArgumentException if {@code n < 0}
     */
    public UF(int n) {
        if (n < 0) throw new IllegalArgumentException();
        count = n;
        parent = new int[n];
        rank = new byte[n];
        for (int i = 0; i < n; i++) {
            parent[i] = i;
            rank[i] = 0;
        }
    }

    /**
     * Returns the canonical element of the set containing element {@code p}.
     *
     * @param  p an element
     * @return the canonical element of the set containing {@code p}
     * @throws IllegalArgumentException unless {@code 0 <= p < n}
     */
    public int find(int p) {
        validate(p);
        while (p != parent[p]) {
            parent[p] = parent[parent[p]];    // path compression by halving
            p = parent[p];
        }
        return p;
    }

    /**
     * Returns the number of sets.
     *
     * @return the number of sets (between {@code 1} and {@code n})
     */
    public int count() {
        return count;
    }
  
    /**
     * Returns true if the two elements are in the same set.
     *
     * @param  p one element
     * @param  q the other element
     * @return {@code true} if {@code p} and {@code q} are in the same set;
     *         {@code false} otherwise
     * @throws IllegalArgumentException unless
     *         both {@code 0 <= p < n} and {@code 0 <= q < n}
     * @deprecated Replace with two calls to {@link #find(int)}.
     */
    @Deprecated
    public boolean connected(int p, int q) {
        return find(p) == find(q);
    }
  
    /**
     * Merges the set containing element {@code p} with the 
     * the set containing element {@code q}.
     *
     * @param  p one element
     * @param  q the other element
     * @throws IllegalArgumentException unless
     *         both {@code 0 <= p < n} and {@code 0 <= q < n}
     */
    public void union(int p, int q) {
        int rootP = find(p);
        int rootQ = find(q);
        if (rootP == rootQ) return;

        // make root of smaller rank point to root of larger rank
        if      (rank[rootP] < rank[rootQ]) parent[rootP] = rootQ;
        else if (rank[rootP] > rank[rootQ]) parent[rootQ] = rootP;
        else {
            parent[rootQ] = rootP;
            rank[rootP]++;
        }
        count--;
    }

    // validate that p is a valid index
    private void validate(int p) {
        int n = parent.length;
        if (p < 0 || p >= n) {
            throw new IllegalArgumentException("index " + p + " is not between 0 and " + (n-1));  
        }
    }

    /**
     * Reads an integer {@code n} and a sequence of pairs of integers
     * (between {@code 0} and {@code n-1}) from standard input, where each integer
     * in the pair represents some element;
     * if the elements are in different sets, merge the two sets
     * and print the pair to standard output.
     *
     * @param args the command-line arguments
     */

}


}