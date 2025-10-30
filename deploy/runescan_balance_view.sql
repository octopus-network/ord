BEGIN;

CREATE OR REPLACE VIEW address_rune_balance_view AS
SELECT 
    address,
    rune_id,
    balance,
    CAST(balance AS NUMERIC) as balance_numeric
FROM address_rune_balance;

CREATE INDEX IF NOT EXISTS idx_address_rune_balance_numeric 
ON address_rune_balance (CAST(balance AS NUMERIC));

CREATE INDEX IF NOT EXISTS idx_address_rune_balance_rune_numeric 
ON address_rune_balance (rune_id, CAST(balance AS NUMERIC) DESC);

COMMIT;
