BEGIN;

CREATE TABLE IF NOT EXISTS public.runes_legacy
(
    rune_id character varying(16) NOT NULL,
    spaced_rune character varying(64) NOT NULL,
    number character varying(20) NOT NULL,
    divisibility smallint DEFAULT 0 NOT NULL,
    symbol character varying(4),
    etching character varying(64) NOT NULL,
    mint_deadline bigint,
    mint_end bigint,
    mint_limit character varying(39) ,
    mints character varying(20) NOT NULL,
    burned character varying(39) NOT NULL,
    premine character varying(39) NOT NULL,
    supply character varying(39) NOT NULL,
    timestamp timestamp with time zone NOT NULL,
    CONSTRAINT runes_legacy_pkey PRIMARY KEY (rune_id),
    CONSTRAINT runes_legacy_spaced_rune_key UNIQUE (spaced_rune)
);

CREATE TABLE IF NOT EXISTS public.rune_balances_legacy
(
    rune_id character varying(16) NOT NULL,
    address character varying(64) NOT NULL,
    amount character varying(39) NOT NULL,
    CONSTRAINT rune_balances_legacy_pkey PRIMARY KEY (rune_id, address),
    CONSTRAINT rune_balances_legacy_rune_id_fkey FOREIGN KEY (rune_id) REFERENCES public.runes_legacy (rune_id)
);

CREATE TABLE IF NOT EXISTS public.rs_transactions_legacy
(
    txid character varying(64) NOT NULL,
    transaction json NOT NULL,
    CONSTRAINT rs_transactions_legacy_pkey PRIMARY KEY (txid)
);

CREATE TABLE IF NOT EXISTS public.rune_transactions_legacy
(
    rune_id character varying(16) NOT NULL,
    txid character varying(64) NOT NULL,
    height bigint NOT NULL,
    timestamp timestamp with time zone NOT NULL,
    CONSTRAINT rune_transactions_legacy_pkey PRIMARY KEY (rune_id, txid),
    CONSTRAINT rune_transactions_legacy_rune_id_fkey FOREIGN KEY (rune_id) REFERENCES public.runes_legacy (rune_id),
    CONSTRAINT rune_transactions_legacy_txid_fkey FOREIGN KEY (txid) REFERENCES public.rs_transactions_legacy (txid)
);

CREATE TABLE IF NOT EXISTS public.address_transactions_legacy
(
    address character varying(64) NOT NULL,
    txid character varying(64) NOT NULL,
    CONSTRAINT address_transactions_legacy_pkey PRIMARY KEY (address, txid),
    CONSTRAINT address_transactions_legacy_txid_fkey FOREIGN KEY (txid) REFERENCES public.rs_transactions_legacy (txid)
);

END;
