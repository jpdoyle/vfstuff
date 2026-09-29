typedef struct List {
   int x;
   struct List* next;
} List;

/*@
// "vals" is an inductive list of ints extracted from the heap
predicate linked_list(List* head; list<int> vals) =
    head == 0 ? vals == nil
              :     head->x    |-> ?val
                &*& head->next |-> ?nextHead
                &*& linked_list(nextHead,?rest)
                &*& vals == cons(val,rest)
              ;

lemma_auto void linked_list_auto()
    requires [?f]linked_list(?head,?vals);
    ensures  [ f]linked_list( head, vals)
        &*&  (head == 0) == (vals == nil)
        ;
{ open linked_list(_,_); }

lemma_auto(append(reverse(a),cons(x,b)))
void append_reverse_cons<t>(list<t> a, t x, list<t> b)
    requires true;
    ensures  append(reverse(a),cons(x,b))
        ==   append(reverse(cons(x,a)),b);
{ append_assoc(reverse(a),{x},b); }

  @*/


int list_length(List* head)
    /*@ requires [?f]linked_list(head,?vals)
            &*&  length(vals) <= INT_MAX; 
      @*/
    /*@ ensures  [ f]linked_list(head, vals)
            &*&  result == length(vals);
      @*/
    /*@ terminates; @*/
{
    int ret = 0;

    while(head)
        /*@ requires [f]linked_list(    head,?loop_vals)
                &*&  ret + length(loop_vals) <= INT_MAX;
          @*/
        /*@ ensures  [f]linked_list(old_head, loop_vals)
                &*&  ret == old_ret + length(loop_vals);
          @*/
        /*@ decreases length(loop_vals); @*/
    {
        head = head->next;
        ++ret;
    }

    return ret;
}

List* list_reverse(List* head)
    /*@ requires linked_list(head,?vals);
      @*/
    /*@ ensures  linked_list(result, reverse(vals));
      @*/
    /*@ terminates; @*/
{
    List* ret = 0;

    while(head)
        /*@ requires linked_list(ret,?ret_vals)
                &*&  linked_list(head,?head_vals)
                &*&  vals == append(reverse(ret_vals),head_vals);
          @*/
        /*@ ensures  linked_list(ret,reverse(vals))
                &*&  linked_list(head,{})
                ;
          @*/
        /*@ decreases length(head_vals); @*/
    {
        List* node = head;
        head = head->next;
        node->next = ret;
        ret = node;
    }

    return ret;
}

List* list_append(List* a, List* b)
    /*@ requires linked_list(a,?a_vals) &*& linked_list(b,?b_vals);
      @*/
    /*@ ensures  linked_list(result, append(a_vals,b_vals));
      @*/
    /*@ terminates; @*/
{
    List** last_pointer = &a;

    while(true)
        /*@ requires *last_pointer |-> ?loop_p
                &*&  linked_list(loop_p,?p_vals)
                &*&  linked_list(b, b_vals);
          @*/
        /*@ ensures  *old_last_pointer |-> ?new_p
                &*&  loop_p == 0
                ?    linked_list(new_p, b_vals)
                :    new_p == loop_p
                &*&  linked_list(loop_p,
                                 append(p_vals,b_vals)); @*/
        /*@ decreases length(p_vals); @*/
    {
        //@ open linked_list(loop_p, p_vals);
        if(*last_pointer) {
            last_pointer = &(*last_pointer)->next;
        } else {
            //@ close linked_list(loop_p, p_vals);
            *last_pointer = b;
            break;
        }
    }

    return a;
}

