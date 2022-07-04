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

    while(*last_pointer)
    {
        last_pointer = &last_pointer->next;
    }

    *last_pointer = b;

    return a;
}

