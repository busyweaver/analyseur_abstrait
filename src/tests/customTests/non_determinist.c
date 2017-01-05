{
    int x;
    int y;
    y = rand(0,3);
    x = 0;
    while(x <= y)
    {
        x = x + rand(0,3);
    }
    
    assert(x <= 3);
        
}
